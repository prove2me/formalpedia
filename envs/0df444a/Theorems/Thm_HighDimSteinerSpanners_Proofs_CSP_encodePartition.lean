-- Prove2me | Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_encodePartition
-- name    : HighDimSteinerSpanners.Proofs.CSP.encodePartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:45.657826+00:00
-- url     : https://prove2.me/theorems/45b8e8e3-187a-4f76-8181-d2387582a6c8
-- title:
--   CSP: encode Partition
-- statement:
--   Encode a disjoint finite partition by labels, using zero for the residual part.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L28-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/WitnessProjection.lean#L28-L127

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section

theorem HighDimSteinerSpanners.Proofs.CSP.encodePartition {N K k : ℕ} (hk : k ≤ K) (M : Finset (Fin N))
    (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N))
    (hMpart : M ⊆ Finset.univ.biUnion A ∪ I_k)
    (hAdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hAIdisjoint : ∀ r, Disjoint (A r) I_k) :
    ∃ τ : Fin N → Fin (K + 1),
      (∀ u ∈ M, τ u = 0 ↔ u ∈ I_k) ∧
      (∀ (r : Fin K) (hr : r.1 < k), ∀ u ∈ M, τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩) ∧
      (∀ u ∈ M, (τ u).1 ≤ k) ∧
      (∀ (r : Fin K) (hr : r.1 < k),
        M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
          M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k)) ∧
      (∀ u, u ∉ M → τ u = 0) := by sorry
