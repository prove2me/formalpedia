-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_fiberIntegral
-- name    : MasulloGRH.elemSchwartz_fiberIntegral
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:08:19.230477+00:00
-- url     : https://prove2.me/theorems/3e1927ec-f12c-4fc4-95c7-74be6b6cae5b
-- title:
--   Integration along the kernel of a quotient map $p\colon E\to E'$ of elementary groups is a continuous linear surjection $\mathcal S(E)\to\mathcal S(E')$
-- statement:
--   **Integration along the fibres of a quotient map of elementary groups** (auxiliary lemma for Theorem D.1.7.1(2)): for a continuous, open, surjective homomorphism $p\colon E\to E'$ of elementary abelian Lie groups, integration over the cosets of $\ker p$ is a continuous linear surjection $\mathcal S(E)\to\mathcal S(E')$.
--
--   For $m,n,r,s\in\mathbb N$ and positive integers $d_0,\dots,d_{s-1}$ let
--   $$E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\textstyle\prod_{i<s}\mathbb Z/d_i\qquad(\mathbb T=\mathbb R/\mathbb Z),$$
--   and let $\mathcal S(E)$ be its Schwartz–Bruhat space (Definition D.1.3.1): the functions $g(x,z,a,b)$ on $E$ that are smooth in $(x,z)\in\mathbb R^m\times\mathbb T^n$ and satisfy $\sup|a|^j\,|x|^i\,\|D^k_{(x,z)}g(x,z,a,b)\|<\infty$ for all $i,j,k$, with the Fréchet topology defined by these seminorms. Let $E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times\prod_{i<s'}\mathbb Z/d'_i$ be a second group of the same kind (all $d'_i$ positive integers) and let $p\colon E\to E'$ be a continuous, open, surjective homomorphism. Its kernel $L=\ker p$ is a closed subgroup of $E$; let $\nu$ be a Haar measure on $L$.
--
--   **Statement.** There is a continuous linear surjection $T\colon\mathcal S(E)\to\mathcal S(E')$ such that for every $g\in\mathcal S(E)$ and every $y\in E$:
--   1. the function $l\mapsto g(y+l)$ is $\nu$-integrable on $L$;
--   2. the value of $Tg$ at $p(y)$ is the integral of $g$ over the coset $y+L$:
--   $$(Tg)(p(y))=\int_L g(y+l)\,d\nu(l).$$
--
--   Examples: for $p\colon\mathbb R^n\to\mathbb T^n$ (kernel $\mathbb Z^n$, counting measure) $T$ is the periodization $g\mapsto\sum_{\ell\in\mathbb Z^n}g(\cdot+\ell)$ onto $C^\infty(\mathbb T^n)$; for a linear surjection $p\colon\mathbb R^m\to\mathbb R^{m'}$ it is integration along the affine fibres; for $p\colon\mathbb Z^r\to 0$ it is summation. This is the elementary case of the coset-integration map $\Phi_H\colon\mathcal S(G)\to\mathcal S(G/H)$ of Theorem D.1.7.1(2): on a stage $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ of a Hausdorff locally compact abelian group $G$, integration over the cosets of a closed subgroup $H$ becomes integration along the kernel $\pi(\Gamma\cap H)$ of the induced homomorphism $\Gamma/k\to\Gamma H/kH$ of elementary groups. The source's proof refers to Lemma D.1.6.18, which treats compact kernels only; here the kernel is an arbitrary closed subgroup (for instance $\mathbb Z\subset\mathbb R$).
--
--   **Formalization Note.** $E$ is the platform's `ElemGroup m n r s d`, written multiplicatively as `Multiplicative (ElemGroup m n r s d)` (so $y+l$ is `y * l`) and equipped with a Borel σ-algebra; `p.ker` carries the subspace topology and the induced σ-algebra, and `ν` is an arbitrary Haar measure on it (`ν.IsHaarMeasure`). The spaces $\mathcal S(E)$, $\mathcal S(E')$ are the platform's `ElemSchwartz` with their seminorm topologies, and `(T g).toFun (Multiplicative.toAdd (p y))` is $(Tg)(p(y))$. The hypotheses $d_i\neq0$ and $d'_i\neq0$ are needed: `ZMod 0 = ℤ` would be a factor on which `ElemSchwartz` imposes no decay. Openness of $p$ is in fact automatic, by the open mapping theorem for $\sigma$-compact groups (`MonoidHom.isOpenMap_of_sigmaCompact`); it is kept among the hypotheses.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 772, 776–777, Lemma D.1.6.18 and Theorem D.1.7.1(2) (elementary case of the coset-integration map, with a closed, not necessarily compact, kernel); auxiliary lemma for the proof of Theorem D.1.7.1(2) (MasulloGRH.schwartzBruhat_cosetIntegral)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem elemSchwartz_fiberIntegral
    {m n r s : ℕ} {d : Fin s → ℕ} {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0)
    [MeasurableSpace (Multiplicative (ElemGroup m n r s d))]
    [BorelSpace (Multiplicative (ElemGroup m n r s d))]
    (p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (hpc : Continuous p) (hpo : IsOpenMap p) (hps : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure] :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d',
      Continuous T ∧ Function.Surjective T ∧
      ∀ (g : ElemSchwartz m n r s d) (y : Multiplicative (ElemGroup m n r s d)),
        Integrable (fun l : p.ker =>
          g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d))))) ν ∧
        (T g).toFun (Multiplicative.toAdd (p y)) =
          ∫ l : p.ker,
            g.toFun (Multiplicative.toAdd (y * (l : Multiplicative (ElemGroup m n r s d)))) ∂ν := by
  sorry

end MasulloGRH
