-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_no_faithful_translation
-- name    : MatchingLogic.Sorted.no_faithful_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:23.193943+00:00
-- url     : https://prove2.me/theorems/5f4d212f-f5e3-45ac-9605-4648e4323ecd
-- title:
--   Sorted: no faithful translation
-- statement:
--   **Corollary 31**, at the Proposition 30 data.
--
--   The paper states Corollary 31 in general: *"There is no translation from
--   many-sorted definedness-free matching logic into any one-sorted definedness-free
--   matching logic that preserves global consequence and reflects derivability."*
--   Its proof is one line — preservation, then Corollary 15 in the target, then
--   reflection would give `Γ ⊢ φ`.
--
--   What is stated here is the **counterexample instance**, not the general
--   statement: there is no target signature and pair of translations that works for
--   the Proposition 30 data. A full rendering would define a translation on the
--   whole source language and state preservation and reflection generally; this is
--   the lemma that instance argument needs, and the general form is future work.
--
--   Three hypotheses are load-bearing and were all missing from a first draft of
--   this statement, which an audit showed to be concretely FALSE without them:
--
--   * `hxy : x ≠ y` — without it `φ3` collapses to a derivable pattern, and the
--     existential body is inhabited;
--   * `StrongLocalCompleteness T Var` — (L) must hold **in the target**, since the
--     paper's proof applies Corollary 15 there. A first draft required it of an
--     unrelated fixed signature;
--   * closedness of the translated patterns, which `global_completeness` requires.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L330-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L330-L348

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]

theorem MatchingLogic.Sorted.no_faithful_translation (hS : MSoundness S3 Var)
    (x y : Var) (hxy : x ≠ y) :
    ¬ ∃ (T : Signature) (tΓ : MPattern S3 Var Srt3.a → Pattern T Var)
        (tφ : MPattern S3 Var Srt3.c → Pattern T Var),
        StrongLocalCompleteness T Var ∧
        (∀ γ ∈ Γ3 (Var := Var) x y, Closed (tΓ γ)) ∧
        Closed (tφ (φ3 (Var := Var) x y)) ∧
        (MGlobalCons (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y) →
          GlobalCons (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y))) ∧
        (Provable (tΓ '' Γ3 (Var := Var) x y) (tφ (φ3 (Var := Var) x y)) →
          MProvable (Γ3 (Var := Var) x y) (φ3 (Var := Var) x y)) := by sorry
