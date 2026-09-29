-- Prove2me | Theorems.Thm_FullLevelTate_eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero
-- name    : FullLevelTate.eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f43eb44a-fffd-505c-a9e4-bf9bfebe5ef2
-- title:
--   Base change of joint injectivity on the rational Tate module
-- statement:
--   Let $q$ and $\lambda$ be primes and $M'$ a natural number, and write $V = \mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(J)$ for [`ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')`](def/ModularCurve_JZeroTateModule.html#L45), the rationalisation of the $\lambda$-adic Tate module $T_\lambda(J) = \{x : \mathbb{N} \to J \mid \lambda^n x_n = 0,\ \lambda x_{n+1} = x_n\}$ of $J =$ [`ModularCurve.FullLevel.Jac q M'`](def/ModularCurve_FullLevelJacobian.html#L85), the product over `Idx q` of copies of the Jacobian $J_H(q^2M', \mathrm{levelH}\,q\,M')$; the monoid homomorphism [`ModularCurve.FullLevel.tateGL2 q M' lam`](def/ModularCurve_FullLevelJacobian.html#L398) sends $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ to the $\mathbb{Z}_\lambda$-endomorphism of $T_\lambda(J)$ induced by the action `gl2Jac` of $g$ on $J$, and each such endomorphism is base changed to $\mathbb{Q}_\lambda$. Let $X$ be a $\mathbb{Q}_\lambda$-module, $sp_0 : V \to X$ a $\mathbb{Q}_\lambda$-linear map, and $K$ a commutative ring which is a $\mathbb{Q}_\lambda$-algebra. Call $v \in V$ cuspidal if for every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ one has $\sum_{t \in \mathbb{Z}/q} \rho(u_t)\rho(g)v = 0$, where $u_t = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ is [`CuspidalType.unipotent q t`](def/CuspidalType_IsCuspidalOfType.html#L27) and $\rho$ denotes the above action. Assume $sp_0$ kills no non-zero cuspidal vector of $V$. Then for every $v' \in K \otimes_{\mathbb{Q}_\lambda} V$ annihilated by all the operators $\sum_t \rho(u_t)\rho(g)$ base changed to $K$, and with $sp_0 \otimes \mathrm{id}_K$ vanishing at $v'$, one has $v' = 0$.
--
--   This is the flat-base-change step transferring a joint injectivity statement on cuspidal vectors of the rational Tate module from $\mathbb{Q}_\lambda$ to an arbitrary $\mathbb{Q}_\lambda$-algebra $K$. It is used in the construction of linear maps out of products of Tate modules in the three cases $q = 2$, $q = 3$ and $q \ge 5$ of the argument over full level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (X : Type) [AddCommGroup X] [Module ℚ_[lam] X]
    (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]] X)
    (K : Type) [CommRing K] [Algebra ℚ_[lam] K] :
    (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q, (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
        sp₀ v = 0 → v = 0) →
      ∀ v' : K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q,
            ((ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam]).baseChange K *
              ((ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]).baseChange K) v' = 0) →
          sp₀.baseChange K v' = 0 → v' = 0 := by sorry
