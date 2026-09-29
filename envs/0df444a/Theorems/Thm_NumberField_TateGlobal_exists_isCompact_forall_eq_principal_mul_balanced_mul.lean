-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul
-- name    : NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/af12d268-d4b9-5805-b66b-5ef2b1ae09a7
-- title:
--   Idele factorisation: principal times balanced dilation times compact
-- statement:
--   Let $F$ be a number field, and let $\alpha$ denote the homomorphism from the idele group $(\mathbb{A}_F)^\times$ (the units of `AdeleRing (𝓞 F) F`) to $\mathbb{R}^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 F) F)`, valued in $\mathbb{R}_{\ge 0}$, by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units. The assertion is that there exists a set $U$ of ideles such that: $U$ is compact; $\alpha(u)=1$ for every $u\in U$; and for every idele $y$ there are $\eta\in F^\times$, ideles $z$ and $u$, and a real number $r$ with $u\in U$, $r>0$, $y=\iota(\eta)\cdot z\cdot u$ where $\iota$ is the map on units induced by the structure map $F\to\mathbb{A}_F$, the finite component of $z$ equal to $1$ in the finite adele ring, every archimedean component of $z$ sent to the real constant $r$ by the embedding `Completion.extensionEmbedding w` of the completion at $w$ into $\mathbb{C}$, for all infinite places $w$, and $\alpha(z)=r^{[F:\mathbb{Q}]}$.
--
--   This is the standard consequence of Fujisaki's compactness theorem for the norm-one idele class group: the idele group is the product of $F^\times$, the one-parameter group of balanced archimedean dilations, and a fixed compact set, with the modulus of the dilation by $r$ equal to $r^{[F:\mathbb{Q}]}$. It is used in the global theory of Tate's zeta integrals, where it reduces estimates for adelic theta-type sums to a scaling parameter and a compact remainder.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal

theorem NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ U : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U ∧ (∀ u ∈ U, ((α u : ℝˣ) : ℝ) = 1) ∧
      ∀ y : (AdeleRing (𝓞 F) F)ˣ, ∃ (η : Fˣ) (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ),
        u ∈ U ∧ 0 < r ∧
        y = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * u ∧
        (z : AdeleRing (𝓞 F) F).2 = 1 ∧
        (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) ∧
        ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F := by sorry
