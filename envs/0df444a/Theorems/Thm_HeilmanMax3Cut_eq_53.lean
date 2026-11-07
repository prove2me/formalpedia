-- Prove2me | Theorems.Thm_HeilmanMax3Cut_eq_53
-- name    : HeilmanMax3Cut.eq_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:28.523611+00:00
-- url     : https://prove2.me/theorems/1027cf36-5b4f-4b1b-8f4c-785048a5bbf6
-- title:
--   Eq. (53) — bilinear inequality on $\mathbb R^2$ for $1/43\le\sigma\le1/2$
-- statement:
--   For every $\sigma\in[1/43,1/2]$ and every pair of partitions $A,B$ of $\mathbb R^2$ into three measurable sets with $\gamma_2(A_i)=\gamma_2(B_i)$ for $i=1,2,3$,
--
--   $$Q^{(2)}_\sigma(A,B)\ \ge\ Q^{(2)}_\sigma(\Theta,-\Theta).$$
--
--   Together with $M_m=M_2$ it gives Theorem 7.1 for $\rho=-\sigma\in[-1/2,-1/43]$.
--
--   Differences from the source:
--   - reading: (53) displayed on p.21 as what suffices for Theorem 7.1; proved in Section 10 for 1/43 ≤ σ ≤ 1/2 → σ ∈ [1/43, 1/2]; reason: this is the range on which the paper asserts and proves (53); the case 0 < σ < 1/43 of Theorem 7.1 is covered by [Hei23] instead (hei23_case)
--   - generalization: Ω (or A, B) a measurable partition of the space into three disjoint sets → IsPartition: measurable cells, almost every point in exactly one cell; reason: every exact partition is one, so the statement specializes to the paper's; Q and γ do not see null sets
--   - encoding: Θ the three 120° sectors; cells i = 1, 2, 3 → Theta = propeller 2 3 (closed sectors sharing null boundary rays); cells Fin 3 = 0, 1, 2; reason: null overlaps do not change Q; the index shift changes no instance
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (53), p.21; proved in Section 10, pp.37–38 ("So, it suffices to let 1/43 ≤ σ ≤ 1/2", p.37; "This proves the bilinear inequality (53)", p.38)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Qstab
import Definitions.Def_HeilmanMax3Cut_Theta
import Definitions.Def_HeilmanMax3Cut_negP
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **Eq. (53): the bilinear inequality on `ℝ²`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (53), p.21, proved in Section 10,
pp.37–38 for `1/43 ≤ σ ≤ 1/2`: "for every pair of partitions `A, B` of `ℝ²` satisfying
`γ₂(Aᵢ) = γ₂(Bᵢ)` for all `i`, `Q_σ^{(2)}(A, B) ≥ Q_σ^{(2)}(Θ, −Θ)`", and p.38: "This proves the
bilinear inequality (53) since (132) is `≥ 0`."

**Formalization Note.** Partitions are `IsPartition` (measurable cells, a.e. point in exactly one
cell); `γ₂` is `gaussian 2`; `Θ` is `propeller 2 3`; `−Θ` is `negP Theta`. -/
theorem eq_53 (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 43 : ℝ) (1 / 2)) (A B : Fin 3 → Set (Space 2))
    (hA : IsPartition A) (hB : IsPartition B) (hAB : ∀ i, gaussian 2 (A i) = gaussian 2 (B i)) :
    Qstab 2 σ Theta (negP Theta) ≤ Qstab 2 σ A B := by sorry

end HeilmanMax3Cut
