-- Prove2me | Theorems.Thm_LeanTT2_algo_no_subject_reduction
-- name    : LeanTT2.algo_no_subject_reduction
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T03:07:58.705867+00:00
-- url     : https://prove2.me/theorems/839711ca-85d8-422c-91f1-5cdd30c3c8a7
-- title:
--   Algorithmic typing lacks subject reduction
-- statement:
--   For every extended fragment, context, and terms α, β, γ, e such that the algorithmic equality relates α to β and β to γ but not α to γ, and e is algorithmically typed at γ: the identity application at β applied to e is algorithmically typed at β, because the application forces checking that β is algorithmically equal to γ; the identity application at α applied to that term is algorithmically typed at α, since it forces checking α against β; the identity application at β applied to e reduces to e; but the identity application at α applied to e is not algorithmically typed at α, because that would require α to be algorithmically equal to γ. Reduction does not preserve algorithmic typing: subject reduction fails for the algorithmic typing judgment.
-- source:
--   M. Carneiro, The Type Theory of Lean, 2019, section 3.1.2 (p. 17).

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

/-!
# Algorithmic typing lacks subject reduction

Thesis section 3.1.2 (page 17): the algorithmic typing judgment, the
variant of typing that uses the algorithmic equality in the conversion
rule, fails subject reduction, directly from the failure of
transitivity. If the algorithmic equality relates α to β and β to γ but
not α to γ, and `e` is algorithmically typed at γ, then:
the identity application at β applied to `e` is algorithmically typed
at β, because the application forces checking that β is algorithmically
equal to γ; the identity application at α applied to that term is
algorithmically typed at α, since it forces checking α against β; but
the identity application at α applied to `e` is not algorithmically
typed at α, because that would require α to be algorithmically equal to
γ. Since the identity application reduces to its argument, this is a
counterexample to subject reduction.
-/

namespace LeanTT2

/-- For every extended fragment, context, and terms `α`, `β`, `γ`, `e`
such that the algorithmic equality relates `α` to `β` and `β` to `γ`
but not `α` to `γ`, and `e` is algorithmically typed at `γ`: the
identity application at `β` applied to `e` is algorithmically typed at
`β`; the identity application at `α` applied to that term is
algorithmically typed at `α`; the identity application at `β` applied
to `e` reduces to `e`; but the identity application at `α` applied to
`e` is not algorithmically typed at `α`. Reduction does not preserve
algorithmic typing. -/
theorem algo_no_subject_reduction (F : Frag.{u}) (Γ : F.Ctx)
    (α β γ e : F.E)
    (hab : F.alg Γ α β) (hbc : F.alg Γ β γ) (hnac : ¬ F.alg Γ α γ)
    (he : F.aty Γ e γ) :
    F.aty Γ (F.app (F.idf β) e) β ∧
    F.aty Γ (F.app (F.idf α) (F.app (F.idf β) e)) α ∧
    F.red Γ (F.app (F.idf β) e) e ∧
    ¬ F.aty Γ (F.app (F.idf α) e) α := by sorry

end LeanTT2
