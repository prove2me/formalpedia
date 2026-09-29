-- Prove2me | Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
-- name    : ModularForm.heckeU_slash_eq_self_of_mem_GammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/6ac38d65-9a4e-5167-9d54-58c2214185cd
-- title:
--   U_q preserves weight-k Γ_H(M)-invariance when q ∣ M
-- statement:
--   Fix an integer $M \ge 1$ (nonzero), a subgroup $H \le (\mathbb{Z}/M)^\times$, a weight $k \in \mathbb{Z}$, and a prime $q$ dividing $M$. Let $\Gamma_H(M)$ denote the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices lying in $\Gamma_0(M)$ whose image under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry modulo $M$ belongs to $H$, viewed via the canonical inclusion as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $f : \mathfrak{H} \to \mathbb{C}$ be a function satisfying $f \mid[k]\, \gamma = f$ for every $\gamma$ in that subgroup, where $\mid[k]$ is the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions on the upper half-plane. The conclusion is that the function
--   $$\mathrm{heckeU}\;k\;q\;f \;=\; \sum_{j=0}^{q-1} f \,\Big|[k]\, \begin{pmatrix} 1 & j \\ 0 & q \end{pmatrix}$$
--   is again invariant: for every $\gamma \in \mathrm{GL}_2(\mathbb{R})$ belonging to $\Gamma_H(M)$ one has $(\mathrm{heckeU}\;k\;q\;f) \mid[k]\, \gamma = \mathrm{heckeU}\;k\;q\;f$. Here the matrices $\begin{pmatrix} 1 & j \\ 0 & q \end{pmatrix}$ are taken as elements of $\mathrm{GL}_2(\mathbb{R})$ through [`ModularForm.heckeMatrix`](def/ModularForm_HeckeOperator.html#L18).
--
--   This is the statement that the operator $U_q$, for a prime $q$ dividing the level $M$, maps weight-$k$ functions invariant under $\Gamma_H(M)$ to functions with the same invariance; it is the first step in defining $U_q$ on modular and cusp forms of level $\Gamma_H(M)$, the variant at level $\Gamma_0(M)$ being proved in the same way. It is used to establish the corresponding stability statement for cusp forms and, through that, the $U_q$- and diamond-stability of the period lattices attached to the modular curves of level $\Gamma_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.heckeU_slash_eq_self_of_mem_GammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    (ModularForm.heckeU k q f) ∣[k] γ = ModularForm.heckeU k q f := by sorry
