-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7f776bb3-bc1e-5d5d-8f99-e5954881c6d9
-- title:
--   Admissible idele class character of ℚ with prescribed component at v and parity
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, let $\chi : (\mathbb{Q}_v)^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism from the units of the $v$-adic completion, and assume that $\chi$ has some conductor exponent $c \in \mathbb{N}$, i.e. `HasConductorExponentAt ℚ v χ c` holds: $\chi$ is trivial on `higherUnitsAt ℚ v c` and for every $m < c$ some element of `higherUnitsAt ℚ v m` is not killed by $\chi$. Let $e \in \mathbb{Z}$ satisfy $\chi(-1) = (-1)^e$ in $\mathbb{C}$. Then there is a homomorphism $\tau$ from the unit group of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ which is an admissible twist — trivial on the image of $\mathbb{Q}^{\times}$, continuous, and of absolute value $1$ everywhere — and which satisfies three further conditions: (i) for every height-one prime $p \neq v$, the local character `localChar τ p` (the composite of $\tau$ with the embedding of $(\mathbb{Q}_p)^{\times}$ into the adelic units at $p$) is trivial on every unit $t$ with both $t$ and $t^{-1}$ in the valuation ring; (ii) `localChar τ v` agrees with $\chi$ on every unit $u$ with both $u$ and $u^{-1}$ in the valuation ring at $v$; and (iii) at every real place $w$ one has `IsArchCompAt ℚ τ w 0 e`, i.e. for all $x \in (\mathbb{Q}_w)^{\times}$ the archimedean component of $\tau$ at $w$ equals $\|x\|^{w.\mathrm{mult} \cdot 0}$ times $(\iota_w(x)/\|x\|)^e$, where $\iota_w$ is the embedding of the completion into $\mathbb{C}$.
--
--   This is the existence statement for a Hecke (idele class) character of $\mathbb{Q}$ whose ramification is concentrated at a single finite place, with prescribed restriction to the local units there and sign $\mathrm{sgn}^e$ at the real place; the parity condition $\chi(-1) = (-1)^e$ is exactly what the global product formula forces. It is used in the cubic-induction step of the Langlands–Tunnell converse argument to twist a Hecke eigensystem so that its local factor at a bad place takes a prescribed shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c)
    (e : ℤ) (he : ((χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) :
    ∃ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ≠ v → IsUnramifiedCharAt τ p) ∧
      (∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        TateGlobal.localChar τ v u = χ u) ∧
      (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e) := by sorry
