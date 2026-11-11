-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_exact_sdp_characterization
-- name    : GuanQinQDP.Restricted.exact_sdp_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:41.80637+00:00
-- url     : https://prove2.me/theorems/a589b2fe-bce5-41d9-b7cd-679b67bb6505
-- title:
--   Theorem 3.5 — exact semidefinite characterization of the profile at a qubit register
-- statement:
--   Let $A$ be any channel on $H_i\otimes H_{\bar\imath}$ whose register $i$ is a qubit. The complement $H_{\bar\imath}$ and the output may have any finite dimension. Let $\gamma\ge1$ and let $\mathcal M$ be a measurement class with event set $\mathcal E(\mathcal M)$. Then
--
--   $$\Delta^{\mathcal M}_{A,i}(\gamma)=\sup_{M\in\mathcal E(\mathcal M)}\ \max_{S\subseteq H_{\bar\imath},\ 1\le\dim S\le2}L_{\gamma,i}(B_{M,S}),$$
--
--   where $B_{M,S}=(I_i\otimes V_S^\dagger)A^\dagger(M)(I_i\otimes V_S)$ is the compressed pullback and $V_S$ an isometry onto $S$. For every event $M$ the inner maximum over subspaces is attained.
--
--   Each inner program is a semidefinite program of dimension at most four, however large the complement is. This characterization is the starting point of the proof of the maximum rule (Theorem 4.1).
--
--   Differences from the source:
--
--   - generalization: complement H_ī = ⊗_{j≠i} H_j of the other registers → arbitrary nonempty finite index type C (register i first, H_i ⊗ C); reason: §3 uses no tensor structure of the complement; a source channel becomes one on ℂ² ⊗ H_ī by the regrouping splitEquiv, so the statement specializes to it
--   - encoding: H_ī a (nonzero) finite-dimensional Hilbert space → [Nonempty C]; reason: excludes only the zero space, on which there are no states
--   - generalization: E(M), the event set of a measurement class on the output sites → an arbitrary set E of effects on an arbitrary finite output; reason: the event set of every class is such a set; no property of the class is used
--   - encoding: max over subspaces S ⊆ H_ī with 1 ≤ dim S ≤ 2 → supremum (compressedValue) over isometries V : ℂ^s → H_ī, s ∈ {1,2}, plus an explicit clause that some V attains it; reason: every such S is the range of an isometry and L_{γ,i}(B_{M,S}) does not depend on the choice
--   - encoding: max in L_{γ,i} → sSup (Lval); reason: the feasible set is nonempty and compact, so the supremum is the maximum
--   - encoding: sup over neighboring pairs and over M ∈ E(M) → sSup (profileFirst) and sSup of the image of E under compressedValue; reason: the sets are nonempty (E = ∅ makes both sides 0) and bounded above by 1, so sSup is the supremum
--   - encoding: Tr[B(ρ − γσ)] → pairValue B ρ σ γ, the real part of the trace; reason: B and ρ − γσ are Hermitian, so the trace is real
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Theorem 3.5 (printed p. 17 / PDF p. 18) and the attainment remark before it, with the standing assumptions of §3 (printed p. 15 / PDF p. 16)

import Definitions.Def_GuanQinQDP_Restricted_Model
open QAlgorithms WildeQIT.EntBreaking
open scoped Matrix

namespace GuanQinQDP.Restricted

/-- Theorem 3.5 (Exact semidefinite characterization), Guan–Qin, STOC 2027 submission #1640,
printed p. 17 / PDF p. 18. Let `A` be any channel on `H_i ⊗ H_ī` whose register `i` is a qubit
(`H_ī` and the output of any finite dimension), `γ ≥ 1`, and `E` a set of events on the output
(every measurement class is such a set). Then

1. for every `M ∈ E` the maximum over subspaces `S ⊆ H_ī`, `1 ≤ dim S ≤ 2`, of
   `L_{γ,i}(B_{M,S})` is attained (by some isometry `V` onto `S`), and
2. `Δ^E_{A,i}(γ) = sup_{M ∈ E} max_{S ⊆ H_ī, 1 ≤ dim S ≤ 2} L_{γ,i}(B_{M,S})`. -/
theorem exact_sdp_characterization {C K : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype K] [DecidableEq K] (A : Matrix (Qubit × C) (Qubit × C) ℂ →ₗ[ℂ] Matrix K K ℂ)
    (hA : IsQuantumChannel A) (γ : ℝ) (hγ : 1 ≤ γ) (E : Set (Matrix K K ℂ))
    (hE : ∀ M ∈ E, IsEffect M) :
    (∀ M ∈ E, ∃ s : ℕ, 1 ≤ s ∧ s ≤ 2 ∧ ∃ V : Matrix C (Fin s) ℂ, Vᴴ * V = 1 ∧
      ∀ s' : ℕ, 1 ≤ s' → s' ≤ 2 → ∀ V' : Matrix C (Fin s') ℂ, V'ᴴ * V' = 1 →
        Lval γ (compress A M V') ≤ Lval γ (compress A M V)) ∧
    profileFirst E A γ = sSup ((fun M => compressedValue A M γ) '' E) := by sorry

end GuanQinQDP.Restricted
