-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_neronGlue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/8d29b28e-8c45-5b7d-8212-f58dfb618ba9
-- title:
--   Glued full Néron model of J₀(N₀p) over O_A
-- statement:
--   Let $p$ be a prime and $N_0 \ge 1$ with $p \nmid N_0$, let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a non-unit of $A$ (the hypothesis `A.LiesOverPrime p`), let $\Lambda$ be a `LevelData N₀ p A` satisfying `Λ.IsJacobian`, and let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, so that $O$ supplies a scheme $G$ with structure morphism $g$ to $\operatorname{Spec}$ of the localisation $\mathbf{Z}_{(p)}$-type ring `baseRing p`, a relative group law $O.L$, a bijection $O.\mathrm{pts}$ between $J_0(N_0p)(\overline{\mathbf{Q}})$, presented as $\mathrm{Pic}^0$ of the base-changed modular function field of level $N_0p$, and the $\overline{\mathbf{Q}}$-points of $g$, widths $O.\mathrm{width}$ and a component map $O.\mathrm{comp}$ on the inertia invariants of $J_0(N_0p)(\overline{\mathbf{Q}})$. Write $K_A$ for the fixed field of the inertia subgroup of $A$ over $\mathbf{Q}$, $O_A = A \cap K_A$ (the ring `shRing A`) with base $\operatorname{Spec} O_A$, $\Lambda.\mathrm{shStr}$ for the induced morphism $\operatorname{Spec} O_A \to \operatorname{Spec}(\mathrm{baseRing}\,p)$, and `shPt A`, `barPt A` for the morphisms $\operatorname{Spec} A \to \operatorname{Spec} O_A$ and $\operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec} A$ induced by the inclusions. The assertion is that there exist a scheme $N_{\mathrm{full}}$, a morphism $g_N \colon N_{\mathrm{full}} \to \operatorname{Spec} O_A$, a relative group law $L_N$ for $g_N$ over $O_A$, an $O_A$-morphism $\iota$ from the base change of $g$ along $\Lambda.\mathrm{shStr}$ to $g_N$, and a map $\mathrm{spec}_N$ from the set of points of $g_N$ over `shPt A` to the component group of $O.\mathrm{width}$ (the $\mathbf{Z}$-dual of the degree-zero character lattice modulo the image of the Gram map of the widths), such that: $L_N$ is commutative; $g_N$ is smooth, separated, locally of finite type and quasi-compact; the restriction map from points of $g_N$ over the identity of $\operatorname{Spec} O_A$ to $K_A$-points of the generic fibre is surjective; $\iota$ is an open immersion; $\iota$ carries the base-changed multiplication of $O.L$ to $L_N$ for points over an arbitrary test morphism $s \colon T \to \operatorname{Spec} O_A$; every point of $g_N$ over `barPt A ≫ shPt A` is $\Lambda.\mathrm{shGenLift}(O.\mathrm{pts}\,x)$ followed by $\iota$ for some $x \in J_0(N_0p)(\overline{\mathbf{Q}})$; $\mathrm{spec}_N$ is additive for $L_N$ on points over `shPt A` and surjective; $\mathrm{spec}_N s = 0$ holds exactly when $s$ is $\Lambda.\mathrm{shLift}\,s_0$ followed by $\iota$ for some point $s_0$ of $g$ over $\Lambda.\sigma_A$; and, for $x$ in the inertia invariants of $J_0(N_0p)(\overline{\mathbf{Q}})$ and $s$ a point of $g_N$ over `shPt A`, if the $\overline{\mathbf{Q}}$-point $\Lambda.\mathrm{shGenLift}(O.\mathrm{pts}\,x)$ followed by $\iota$ equals `barPt A` followed by $s$, then $O.\mathrm{comp}\,x = \mathrm{spec}_N s$.
--
--   This is the construction of the full Néron model of $J_0(N_0p)$ over the ring $O_A = A \cap K_A$, obtained by gluing translates of the base change of the identity component along its generic fibre, together with the data identifying its group of components with the Kirchhoff-type component group attached to the widths. It is the raw input from which [`ModularCurve.JZeroNeronObjectAtP.nonempty_neronExtension`](thm.html#ModularCurve.JZeroNeronObjectAtP.nonempty_neronExtension) produces the Néron extension property used in the study of the reduction of $J_0(N_0p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_neronGlue
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ (Nfull : Scheme.{0}) (gN : Nfull ⟶ shBase A) (LN : RelativeGroupLaw ↥(shRing A) gN),
      LN.IsCommutative ∧
      (Smooth gN ∧ IsSeparated gN ∧ LocallyOfFiniteType gN ∧ QuasiCompact gN) ∧
      Function.Surjective (genericFibreRestrict ↥(shRing A) ↥(invField A) gN (𝟙 (shBase A))) ∧
      ∃ (openImm : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) gN)
        (specN : SchemeHomOver (shPt A) gN → componentGroup O.width),
        IsOpenImmersion openImm.1 ∧
        (∀ {T : Scheme.{0}} (s : T ⟶ shBase A)
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
          NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).mul s x y) openImm =
            LN.mul s (NeronModelInfra.schemeHomOverComp x openImm) (NeronModelInfra.schemeHomOverComp y openImm)) ∧
        (∀ y : SchemeHomOver (barPt A ≫ shPt A) gN,
          ∃ x : JZero (N₀ * p), NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) openImm = y) ∧
        (∀ s s' : SchemeHomOver (shPt A) gN, specN (LN.mul (shPt A) s s') = specN s + specN s') ∧
        Function.Surjective specN ∧
        (∀ s : SchemeHomOver (shPt A) gN,
          specN s = 0 ↔ ∃ s₀ : SchemeHomOver Λ.σA O.g, NeronModelInfra.schemeHomOverComp (Λ.shLift s₀) openImm = s) ∧
        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver (shPt A) gN),
          (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) openImm).1 = barPt A ≫ s.1 →
            O.comp x = specN s) := by sorry
