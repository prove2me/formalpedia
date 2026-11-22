-- Prove2me | Theorems.Thm_MatchingLogic_global_completeness_of_localCompleteness
-- name    : MatchingLogic.global_completeness_of_localCompleteness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:36.049842+00:00
-- url     : https://prove2.me/theorems/e6a44e3c-5097-4732-b649-d32fd31906bb
-- title:
--   Matching Logic: global completeness of local Completeness
-- statement:
--   **Corollary 15 with (S) discharged.**
--
--   Entry point (ii) of the paper's challenge is Corollary 15 *with (L) and (S)
--   assumed*, which is `global_completeness` above. But (S) is not an assumption
--   here — `soundness` proves it — so it can be supplied rather than hypothesised,
--   leaving (L) as the only remaining black box.
--
--   This is entry point (ii) in full, plus (S) discharged -- which (ii) permitted
--   us to assume, so it is beyond (ii) rather than part of (iii). Entry point (iii)
--   asks for (L) to be discharged as well; that is done in `MatchingLogic/EntryIII/`
--   (see `strongLocalCompleteness` and `global_completeness_entryIII` in
--   `EntryIII/Conclusion.lean`), via Theorem 73, Lemmas 80--81, and strong local
--   completeness Theorem 83 of Chen and Rosu, *Matching μ-Logic*, 2019 technical
--   report (https://hdl.handle.net/2142/102281), the paper's reference [5].
--   The theorem below deliberately keeps
--   (L) as a hypothesis: it holds at an *arbitrary* element-variable type, whereas
--   the (iii) discharge is at the paper's scope `[Denumerable Var]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryPoints.lean#L49-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryPoints.lean#L49-L54

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Completeness
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Tactic.Finiteness.Attr
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.global_completeness_of_localCompleteness
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ Provable Γ φ := by sorry
