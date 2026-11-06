-- Prove2me | Theorems.Thm_GnpColoring_lemma_3_27
-- name    : GnpColoring.lemma_3_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:21.011502+00:00
-- url     : https://prove2.me/theorems/78256a97-9d13-499a-8289-f05feeae14cf
-- title:
--   Lemma 3.27 — $\lambda_{\min}(A_\partial)\ge-C'\sqrt d$
-- statement:
--   There is an absolute constant $C'>0$ such that for all $0<\eta<1/2$, $A\ge1$ and $C>0$, for all sufficiently large $d$, with probability $1-o(1)$ as $n\to\infty$ over $G\sim G(n,d/n)$: for every valid block partition $S$ of $G$ (parameters $d,\eta,A,C$, any $D$),
--
--   $$\lambda_{\min}(A_\partial)\ge-C'\sqrt d,$$
--
--   where $A_\partial$ is the adjacency matrix of the edges of $G$ with an endpoint in $S$.
--
--   This controls the possibly negative term of Corollary 3.26.
--
--   Differences from the source:
--   - encoding: $G\sim G(n,d/n)$, "with probability $1-o(1)$" → probability under the Erdős–Rényi law with edge probability $d/n$ clamped into $[0,1]$ tends to $1$ as $n\to\infty$; reason: the clamp only affects $n<d$, which the limit never sees
--   - encoding: absolute constant $C$ → $C'$; reason: $C$ already names the weight constant
--   - reading: $\lambda_{\min}(A_\partial)\ge-C\sqrt d$ for the partition at hand → $z^\top A_\partial z\ge-C'\sqrt d\,\|z\|^2$ for all $z$ and for every valid partition, inside the event; reason: the proof notes the bound "applies even though U depends on G"
--   - generalization: valid partitions for the diameter constant $D=D(\eta,A,C)$ fixed in Definition 3.2 before $d$ → every $D>0$, quantified inside the event, after $d_0$, so the bound is uniform in $D$; reason: the proof (pp.33–34) uses only the degree bound on $U$ and the tree/unicyclic structure, never the diameter condition; taking $D=D(\eta,A,C)$ gives the source's statement
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 3.27, p.33

import Mathlib
import Definitions.Def_GnpColoring_boundaryAdj
import Definitions.Def_GnpColoring_IsValidPartition
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical
open Finset
open Filter Topology

namespace GnpColoring

/-- **Lemma 3.27 (smallest eigenvalue of `A_∂`).** There is an absolute constant `C' > 0` such that for
all `0 < η < 1/2`, `A ≥ 1` and `C > 0`, for all sufficiently large `d`, with probability `1 − o(1)` over
`G ∼ G(n, d/n)`: for every valid block partition `S` of `G`, `λ_min(A_∂) ≥ −C'√d`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 3.27, p.33: "Let G ∼ G(n, d/n), assume A ≥ 1, and take d sufficiently large. There is
an absolute constant C such that, with probability 1 − o(1) as n → ∞, λ_min(A_∂) ≥ −C√d."

**Formalization Note** The paper's absolute constant `C` is renamed `C'` (`C` is the weight
constant of `α = C log d`). The partition is quantified inside the event (proof, p.33: "This
applies even though U depends on G"). `λ_min(A_∂) ≥ −C'√d` is the Rayleigh form
`zᵀA_∂z ≥ −C'√d ‖z‖²` for every `z ∈ ℝ^V`. `G(n, d/n)` is `LPCommunity.SBMRecovery.erProb n (d/n)`
(edge probability clamped into `[0,1]`, which matters only for `n < d`); "with probability
`1 − o(1)`" is convergence of the probability to `1` as `n → ∞` with all constants fixed first. -/
theorem lemma_3_27 :
    ∃ C' : ℝ, 0 < C' ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 → ∀ A : ℝ, 1 ≤ A → ∀ C : ℝ, 0 < C →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (d / n) (fun G =>
          ∀ (D : ℝ) (S : Finset (Fin n)), IsValidPartition G d η A C D S →
            ∀ z : Fin n → ℝ,
              -(C' * Real.sqrt d) * ∑ v, z v ^ 2 ≤ ∑ u, ∑ v, boundaryAdj G S u v * z u * z v))
        atTop (𝓝 1) := by sorry

end GnpColoring
