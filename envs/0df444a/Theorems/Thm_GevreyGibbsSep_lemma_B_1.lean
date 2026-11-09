-- Prove2me | Theorems.Thm_GevreyGibbsSep_lemma_B_1
-- name    : GevreyGibbsSep.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:40:44.532993+00:00
-- url     : https://prove2.me/theorems/55bcd015-4c64-4455-9fa0-471bc986c7a2
-- title:
--   Lemma B.1 — null coupling: a run agrees with the null run until the patch is hit
-- statement:
--   Let $A$ be a sampling algorithm with the oracle of order $k\in\mathbb N\cup\{\infty\}$, and let the instance have density equal to $\kappa>0$ at every point outside a closed set $\Omega\subseteq\mathbb T^d$ (for instance a bump $p_g$ on the patch $\Omega_g$). Let $X^{\mathrm{null}}_n,\widehat X^{\mathrm{null}}_n$ be the null run (B5), fed the flat answer $(\log\kappa,0,0,\dots)$, and let
--   $$\tau(\omega)=\inf\{n\ge1:\ X^{\mathrm{null}}_n(\omega)\in\Omega\},\qquad\inf\emptyset=\infty .$$
--   Then for every seed $\omega$,
--   $$X_n(\omega)=X^{\mathrm{null}}_n(\omega)\ \ \forall n\le\tau(\omega),\qquad \widehat X_n(\omega)=\widehat X^{\mathrm{null}}_n(\omega)\ \ \forall n<\tau(\omega).$$
--
--   Until the first query lands in the patch, the algorithm sees only flat answers and behaves exactly as on a blank landscape; this is the coupling behind the hide-and-seek lower bound.
--
--   **Formalization Note** The statement is given for each $n$: if none of $X^{\mathrm{null}}_1,\dots,X^{\mathrm{null}}_n$ lies in $\Omega$ (i.e. $n<\tau$), then $X_{n+1}=X^{\mathrm{null}}_{n+1}$ and $\widehat X_n=\widehat X^{\mathrm{null}}_n$.
--
--   Differences from the source:
--   - generalization: the instance is a bump $p_g$ on the patch $\Omega_g$ → any instance whose density equals $\kappa>0$ at every point outside the closed set $\Omega$; reason: the proof uses only this property; every bump has it
--   - encoding: $X_n=X^{\mathrm{null}}_n$ for $n\le\tau$, $\widehat X_n=\widehat X^{\mathrm{null}}_n$ for $n<\tau$ → for each $n$, if $X^{\mathrm{null}}_1,\dots,X^{\mathrm{null}}_n\notin\Omega$ then $X_{n+1}=X^{\mathrm{null}}_{n+1}$ and $\widehat X_n=\widehat X^{\mathrm{null}}_n$; reason: the same assertions with $\tau$ unfolded and queries indexed from $0$
--   - generalization: output maps $\Psi_n$, $n\ge1$ → an output $\widehat X_0$ with no query is also allowed; reason: a larger class of algorithms can only lower $N_{\mathrm{cl}}$, so the lower bound is at least as strong
--   - reading: a seed $\omega\sim P$ and maps $Q_n,\Psi_n$, with the output law the distribution over the seed → an arbitrary probability space of seeds and jointly measurable $Q_n,\Psi_n$; reason: the output law is only defined for measurable maps; the seed space is not restricted to countable ones
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: the order-$k$ answer $\phi_k(p,x)=(\nabla^{\otimes j}\log\bar p(x))_{j=0}^{k}$ at a representative of $x$, $k\in\mathbb N\cup\{\infty\}$ → the family of all iterated partials $\partial_{i_1}\cdots\partial_{i_j}\log\bar p$ of every order $j$ at the $[0,2\pi)^d$ representative of $x$, with the entries of order $j>k$ set to $0$, and $k\in\mathbb N\cup\{\top\}$; reason: the entries of order $j\le k$ are the components of $\nabla^{\otimes j}\log\bar p(x)$ and the padded zeros carry no information, so every algorithm sees the same answers
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Lemma B.1, Eqs. (B6)–(B7), p.35

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_toTorus
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_SamplingAlg
import Definitions.Def_GevreyGibbsSep_runAnswers
import Definitions.Def_GevreyGibbsSep_nullAnswer

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Lemma B.1 (null coupling), arXiv:2608.24527 (sha256 d4fd40eb…), Eqs. (B6)–(B7), p.35. If the
density of the instance equals `κ > 0` at every point outside the closed patch `Ω`, then for every
seed `ω` and every `n`: if none of the null queries `X^null_1, …, X^null_n` lies in `Ω` (that is,
`n < τ(ω)` for the first hitting time `τ` of (B6)), the run on the instance and the null run agree,
`X_{n+1} = X^null_{n+1}` and `X̂_n = X̂^null_n`. This is (B7): `X_m = X^null_m` for `m ≤ τ` and
`X̂_m = X̂^null_m` for `m < τ`.

**Formalization Note** Queries are indexed from `0`: `A.Q n ω O` is `X_{n+1}`. The hypothesis
uses only that the density equals `κ` off `Ω`, which is all the proof uses of the bump `p_g`. -/
theorem lemma_B_1 {d : ℕ} (A : SamplingAlg d) (k : ℕ∞) (V : (Fin d → ℝ) → ℝ)
    (Ω : Set (Torus d)) (κ : ℝ) (hΩ : IsClosed Ω) (hκ : 0 < κ)
    (hflat : ∀ x : Fin d → ℝ, toTorus x ∉ Ω → Real.exp (- V x) / partitionFn V = κ)
    (ω : A.Ω) (n : ℕ) (hn : ∀ m < n, A.Q m ω (fun _ => nullAnswer d κ) ∉ Ω) :
    A.Q n ω (runAnswers A k V ω n) = A.Q n ω (fun _ => nullAnswer d κ) ∧
    A.Ψ n ω (runAnswers A k V ω n) = A.Ψ n ω (fun _ => nullAnswer d κ) := by sorry

end GevreyGibbsSep
