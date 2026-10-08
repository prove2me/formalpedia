-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_contraction
-- name    : HarrisonReimanRBM.Orthant.contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:15.943552+00:00
-- url     : https://prove2.me/theorems/d06fbeeb-f5c3-46bd-92ee-a51e6e5b9c29
-- title:
--   Contraction: $\|\pi(y)-\pi(y')\|\le\alpha\|y-y'\|$ on $[0,T]$ when the maximal column sum of $Q$ is $\alpha<1$
-- statement:
--   Let $K\ge1$ and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal whose maximal column sum satisfies
--   $$\alpha=\max_{1\le j\le K}\sum_{i=1}^K q_{ij}<1.$$
--   Fix $x\in C_S$, $T>0$, and let $\pi$ be the map $\pi(y)(t)=\sup_{0\le s\le t}[y(s)Q-x(s)]^+$ (componentwise). Equip paths on $[0,T]$ with the norm $\|y\|=\max_{1\le j\le K}\sup_{0\le t\le T}|y_j(t)|$. Then for all paths $y,y'$ continuous on $[0,T]$,
--   $$\|\pi(y)-\pi(y')\|\le\alpha\,\|y-y'\|.$$
--
--   Hence $\pi$ is a contraction of the complete metric space $C_0[0,T]$, which yields the unique fixed point of (13)–(14).
--
--   **Formalization Note** The paper writes $\|Q\|=\alpha<1$ with $\|\cdot\|$ the maximal **row** sum. Under the paper's row-vector convention $(yQ)_j=\sum_i y_iq_{ij}$, the Lipschitz constant of $y\mapsto yQ$ in the max-norm is the maximal **column** sum, and with the printed reading the inequality is false: for $K=3$, $q_{13}=q_{23}=0.9$ and all other entries $0$ (spectral radius $0$, row sums $\le0.9$), $x\equiv0$, $y(s)=(s,s,0)$, $y'\equiv0$ on $[0,1]$ gives $\pi_3(y)(1)=1.8$ while $\|y-y'\|=1$. The statement therefore assumes the maximal column sum is $\alpha<1$; the Veinott step applied to $Q^\top$ provides such a rescaling. The paper restricts $y,y'$ to $C_0[0,T]$; the inequality holds for all continuous $y,y'$ on $[0,T]$, and that stronger form is stated.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 304, proof of Theorem 1 (the contraction inequality following the definition of the norm on C[0, T])

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Proof of Theorem 1, p. 304: if `Q ≥ 0` has zero diagonal and maximal column sum
`α < 1` (the norm for which `y ↦ yQ` is a contraction under the row-vector convention), then
for `x ∈ C_S` and `y, y'` continuous on `[0, T]`,
`‖π(y) − π(y')‖ ≤ α ‖y − y'‖` in the norm `max_j sup_{0 ≤ t ≤ T} |·_j(t)|`. -/
theorem contraction {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQd : ∀ j, Q j j = 0) (α : ℝ) (hα : maxColSum Q = α)
    (hα1 : α < 1) (x : ℝ → Fin K → ℝ) (hx : IsCPlus x) (T : ℝ) (hT : 0 < T)
    (y y' : ℝ → Fin K → ℝ) (hy : ContinuousOn y (Set.Icc 0 T))
    (hy' : ContinuousOn y' (Set.Icc 0 T)) :
    supNormOn T (piMap Q x y - piMap Q x y') ≤ α * supNormOn T (y - y') := by sorry

end HarrisonReimanRBM.Orthant
