-- Prove2me | Theorems.Thm_OAI_Dixmier_DirectSumObstruction_scaled_direct_sum_obstruction
-- name    : OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:43:32.168703+00:00
-- url     : https://prove2.me/theorems/5135b34b-0433-4c12-9183-b1e454645644
-- title:
--   Scaled direct-sum obstruction: representations with $\|\pi(g)\|\le 1+t\kappa$ for every $t>0$ that are not similar to unitary ones
-- statement:
--   Let $G$ be a group (no topology or countability is assumed). For an integer $k\ge1$ let $\mathcal H_k=\ell^2(G;\mathbb{C}^k)$ be the Hilbert space of functions $\xi:G\to\mathbb{C}^k$ with $\|\xi\|^2=\sum_{x\in G}\|\xi(x)\|^2<\infty$, and let $\lambda$ be the left translation representation, $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$. For $x\in G$ let $\mathrm{ev}_x:\mathcal H_k\to\mathbb{C}^k$, $\xi\mapsto\xi(x)$, be evaluation at $x$, and let $\iota_x:\mathbb{C}^k\to\mathcal H_k$ be the inclusion sending $v$ to the function equal to $v$ at $x$ and to $0$ elsewhere. For a bounded operator $F$ on $\mathcal H_k$ we use
--
--   - its *row* $\mathrm{ev}_1F:\mathcal H_k\to\mathbb{C}^k$ and its *column* $F\iota_1:\mathbb{C}^k\to\mathcal H_k$ at the identity $1\in G$;
--   - its blocks $F_{x,y}=\mathrm{ev}_xF\iota_y$, which are $k\times k$ matrices, and its *kernel energy* $\mathcal E(F)=\sum_{s\in G}\|F_{1,s}\|_{\mathrm{HS}}^2$, where $\|B\|_{\mathrm{HS}}^2=\sum_{a,b}|B_{ab}|^2$ is the squared Hilbert–Schmidt (Frobenius) norm;
--   - its *coboundary* $g\mapsto F-\lambda(g)F\lambda(g^{-1})$.
--
--   Let $(k_j)_{j\in\mathbb N}$ be positive integers, let $\kappa\ge0$ and $t>0$ be real numbers, and for every $j$ let $A_j,T_j$ be bounded operators on $\mathcal H_{k_j}$ such that, for all $j\in\mathbb N$ and $g\in G$:
--
--   1. $A_j\lambda(g)=\lambda(g)A_j$;
--   2. $\|\mathrm{ev}_1T_j\|\le\kappa$ and $\|(A_j-T_j)\iota_1\|\le\kappa$;
--   3. $\|T_j-\lambda(g)T_j\lambda(g^{-1})\|\le\kappa$;
--   4. $\mathcal E(A_j)/k_j\to+\infty$ as $j\to\infty$.
--
--   Let $\mathcal H=\bigoplus_{j\in\mathbb N}\mathcal H_{k_j}$ be the Hilbert direct sum and $\mathcal K=\mathcal H\oplus\mathcal H$, with $\|(x,y)\|^2=\|x\|^2+\|y\|^2$. Then there is a group homomorphism $\pi$ from $G$ into the bounded linear operators on $\mathcal K$ such that
--
--   $$
--   \|\pi(g)\|\le 1+t\kappa\qquad\text{for all }g\in G,
--   $$
--
--   and $\pi$ is not similar to a unitary representation: there is no bounded linear bijection $S$ of $\mathcal K$ with bounded inverse such that $\|S\pi(g)S^{-1}x\|=\|x\|$ for all $g\in G$ and $x\in\mathcal K$.
--
--   Compared with the unscaled obstruction (the case $t=1$), the free parameter $t>0$ shows that one family of stage operators produces non-unitarizable representations whose norms are uniformly as close to $1$ as desired. This is how the bound $\|\pi(g)\|\le1+\varepsilon$, for every $\varepsilon>0$, is obtained for non-amenable groups.
--
--   **Formalization Note** The stage $\mathcal H_{k_j}$ is `Stage G k j`, an `lp` space with fibres `EuclideanSpace ℂ (Fin (k j))`, and $\mathcal K$ is `Carrier G k`, the space `WithLp 2 (H × H)` over the `lp` Hilbert sum `H` of the stages. Row, column, coboundary and energy are `KernelObstruction.row (T j) 1`, `KernelObstruction.col (A j - T j) 1`, `coboundary KernelObstruction.translation (T j) g` and `KernelObstruction.energy`; the energy is an infinite sum (`tsum`), and $k_j$ is cast to a real number in the ratio. The representation is a monoid homomorphism into the continuous linear operators, and `SimilarToUnitary` asks for a continuous linear equivalence $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/ScaledObstruction.lean#L28-L61

import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete

open OAI OAI.Dixmier OAI.Dixmier.DirectSumObstruction
open Filter
variable {G : Type*} [Group G]

theorem OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j - T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + t * κ) ∧ ¬ SimilarToUnitary π := by sorry
