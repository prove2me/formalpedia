-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
-- name    : ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/52e068f6-bd2b-5834-b40c-2ac66603e926
-- title:
--   Unipotent γ acts on q-expansions as the ζᵇ-twist
-- statement:
--   Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ (an element of `Idx q`, i.e. of `primitiveRoots q (AlgebraicClosure ℚ)`), and let $u \in \overline{\mathbb{Q}}^{\times}$ be a unit whose underlying element is $\zeta$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and suppose that its reduction modulo $q$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ is the unipotent matrix $\begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ for some $t \in \mathbb{Z}/q$. Let $f$ be an element of `fieldBar q M'`, the subfield of $\overline{\mathbb{Q}}((Q))$ generated over $\overline{\mathbb{Q}}$ by the function field of level $\Gamma_H(q^2M')$, where $H \le (\mathbb{Z}/q^2M')^{\times}$ is the kernel of reduction to $(\mathbb{Z}/q)^{\times}$. Then the Laurent series attached to `levelAutBar q M' ζ γ f` is the twist of the Laurent series of $f$ by $u^{b}$, where $b = \gamma_{01}$: its $n$-th coefficient is $\zeta^{bn}$ times the $n$-th coefficient of $f$. Here `levelAutBar q M' ζ γ` is, by definition, a choice of $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of `fieldBar q M'` satisfying `IsLevelAutBar q M' ζ γ τ` — namely, for all weights $k$, all modular forms $f, g$ of level $\Gamma_H(q^2M')$ with integral $q$-expansions and $g \ne 0$, and every embedding $\iota \colon \overline{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the series $\iota(\tau(f/g))$ times the $q$-expansion of $g \mid_k \gamma^{\sharp}$ equals that of $f \mid_k \gamma^{\sharp}$ — and is the identity if no such $\tau$ exists.
--
--   This is the classical computation of the action, on $q$-expansions along one geometric component of the modular curve of level $K(q)K_0(M')$, of the level automorphism attached to an element of $\Gamma_0(M')$ that is unipotent modulo $q$: it acts by $Q \mapsto \zeta^{b}Q$. It is used in the analysis of the semistable covering at $q$, in the existence statement for such twists for arbitrary $\gamma \in \Gamma_0(M')$, and in showing that $\tau(\bar{j}) - c$ is a unit for the relevant constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hγu : ∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val)
    (f : fieldBar q M') :
    ((levelAutBar q M' ζ γ f : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qTwist (u ^ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1))
        (f : LaurentSeries (AlgebraicClosure ℚ)) := by sorry
