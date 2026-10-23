-- Prove2me | Theorems.Thm_FragLOB_Collapse_proof_thm1_separable
-- name    : FragLOB.Collapse.proof_thm1_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:43.250645+00:00
-- url     : https://prove2.me/theorems/cab8f6d4-3c54-42a0-9a75-afa843756374
-- title:
--   Proof of Theorem 1, p. 1332 — problem (13) is separable in γ (F-a.e.)
-- statement:
--   Let $F$ be a probability distribution of investor types on $[0,\infty)$ with finite mean $\int\gamma\,dF(\gamma) < \infty$. Fix arbitrary delays $d_1,\dots,d_N \in \mathbb R$ and write
--   $u_\gamma(p) = p_0\gamma\tilde r_0 + \sum_{i=1}^N p_i(\gamma\tilde r_i - d_i)$ for the payoff of a type-$\gamma$ investor using the routing vector $p$. Let $\pi \in \mathcal P$ be a routing decision (measurable, with $\pi(\gamma)$ in the simplex for every $\gamma \ge 0$). Then $\pi$ maximizes the aggregate payoff over all routing decisions,
--
--   $$\int_0^\infty u_\gamma(\pi'(\gamma))\,dF(\gamma) \le \int_0^\infty u_\gamma(\pi(\gamma))\,dF(\gamma) \quad\text{for all } \pi' \in \mathcal P,$$
--
--   if and only if, for $F$-almost every type $\gamma$, $\pi(\gamma)$ maximizes $u_\gamma$ over the simplex $\{p : p_i \ge 0,\ \sum_{i=0}^N p_i = 1\}$.
--
--   This is the separability of problem (13) in $\gamma$ invoked in the proof of Theorem 1: it turns optimality of the aggregated problem into individual rationality (10), type by type, and back.
--
--   **Formalization Note.** The pointwise statement holds only $F$-almost everywhere: changing $\pi$ on an $F$-null set of types does not change any integral, so optimality in (13) cannot force rationality at every single type (for $N=1$, $\lambda_1 = 0$, $\Lambda = 2$, $\mu = \beta_1 = 1$, $\tilde r = (-1, 1)$ and $F$ exponential, altering the threshold policy at $\gamma = 5$ keeps it optimal but makes type $5$ irrational). The finite mean makes every objective a genuine (integrable) integral; without it Lean's integral of a non-integrable function would be $0$.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), p. 1332, proof of Theorem 1 (separability of (13) with respect to γ)

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem proof_thm1_separable {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) (hpi : IsRouting pi) :
    (∀ pi' : ℝ → Fin (N + 1) → ℝ, IsRouting pi' →
        ∫ γ, payoff M d γ (pi' γ) ∂F ≤ ∫ γ, payoff M d γ (pi γ) ∂F) ↔
      ∀ᵐ γ ∂F, IsBestResponse M d γ (pi γ) := by sorry

end FragLOB.Collapse
