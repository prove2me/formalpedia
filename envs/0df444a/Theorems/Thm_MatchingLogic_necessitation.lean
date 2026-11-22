-- Prove2me | Theorems.Thm_MatchingLogic_necessitation
-- name    : MatchingLogic.necessitation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:54.570815+00:00
-- url     : https://prove2.me/theorems/51b16be8-64ea-405a-8734-eec72eb0d747
-- title:
--   Matching Logic: necessitation
-- statement:
--   **Lemma 5 (necessitation).**  If `Γ ⊢ ψ` then `Γ ⊢ [p]ψ` for every word `p`.
--
--   The paper's proof, for a single coordinate `e`: the tautology
--   `ψ → ((ψ → ⊥) → ⊥)` with modus ponens gives `Γ ⊢ ¬ψ → ⊥`; framing in position
--   `i` with `⊤` elsewhere gives `Γ ⊢ ⟨e⟩¬ψ → σ(⊤,…,⊥,…,⊤)`; propagation of `⊥`
--   gives `⊢ σ(⊤,…,⊥,…,⊤) → ⊥`; composing is propositional. Then iterate along `p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L292-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean#L292-L297

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.necessitation {Γ : Set (Pattern S Var)} {ψ : Pattern S Var}
    (h : Provable Γ ψ) (p : List (Coord S)) : Provable Γ (boxes p ψ) := by sorry
