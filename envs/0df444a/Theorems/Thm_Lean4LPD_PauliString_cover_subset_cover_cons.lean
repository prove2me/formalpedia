-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_cover_subset_cover_cons
-- name    : Lean4LPD.PauliString.cover_subset_cover_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:47.12192+00:00
-- url     : https://prove2.me/theorems/01f79329-1893-4412-975b-58ba5b1545cd
-- title:
--   Pauli String: cover subset cover cons
-- statement:
--   The step of the containment induction: once the head generator `G` has fired, the strings it
--   produces are supported in `S ∪ supp G`, and — because the rest of the layer is disjoint from
--   `G` — the *remaining* generators that can still fire are exactly those that could already fire
--   from `S`. So the light cone does not compound within a layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L298-L315
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L298-L315

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.cover_subset_cover_cons {G : PauliString n} {Gs : List (PauliString n)}
    (hG : ∀ H ∈ Gs, Disjoint (support G) (support H))
    (hGS : (support G ∩ S).Nonempty) (hT : T ⊆ S ∪ support G) :
    cover Gs T ⊆ cover (G :: Gs) S := by sorry
