-- Prove2me | Theorems.Thm_NishtAbel2024_guarded_theorem10_original_coherent
-- name    : NishtAbel2024.guarded_theorem10_original_coherent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:58:33.366229+00:00
-- url     : https://prove2.me/theorems/faee4722-bd52-4262-8db6-cd28572c308a
-- title:
--   Guarded constraint-direction lemma for the existing size model
-- statement:
--   In the existing NishtAbel2024 Lean comparison model, fix a size variable i whose flexible polarity is strictly positive or negative. Assume i is absent from the left type according to the existing SizeOccursIn predicate, all occurrences recognized by SizeOccursFixPol in the right type have the stated common polarity and compatible fixpoint kind, and the existing polarity-hygiene hypotheses hold. For the auxiliary occurrence-coherent comparison, every generated constraint mentioning i belongs to the set produced by the specified product of comparison, flexible and occurrence polarities, comparing an arbitrary size expression a with i. The allowed a is an arbitrary SizeExp; this is the original formal statement, while the thesis describes a variable j. The auxiliary relation is a strict restriction of existing comparison, and its derivability from source inference is unproved. This is a guarded lemma, not the full theorem in the thesis.
-- source:
--   Auxiliary guard for the current Lean formalization, inspired by Kanstantsin Nisht, Type-Based Termination Checking in Agda (master’s thesis supervised by Andreas Abel, 2024), https://knisht.github.io/agda/msc.pdf, §6.3.3–6.3.4, pp. 51–52. This exact guard is an additional condition not stated as a theorem of the thesis; whether source-generated comparisons satisfy it is unproved. The proposition retains the hypotheses and conclusion of the original formal Theorem 10 conjunct, but replaces unrestricted comparison by this auxiliary guarded relation. The current formal conclusion permits an arbitrary SizeExp on the other side of the constraint, whereas the thesis text formulates this using a variable j.

import Definitions.Def_NishtAbel2024_ComparisonCoherenceAux

namespace NishtAbel2024

theorem guarded_theorem10_original_coherent :
    ∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      CoherentCompareTypes i Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0) := by
  sorry

end NishtAbel2024
