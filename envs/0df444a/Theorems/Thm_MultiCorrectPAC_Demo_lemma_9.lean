-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_9
-- name    : MultiCorrectPAC.Demo.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:32.94037+00:00
-- url     : https://prove2.me/theorems/f1d59307-2b69-4fad-93fd-02d69c314544
-- title:
--   Lemma 9 — d∩_N ≤ d∩_DS, d_pair ≤ d∩_DS, d∩_N ≤ d∩_pack; DS and packed witnesses restrict to subsequences
-- statement:
--   For every class $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$,
--   $$d^\cap_{\mathrm N}(\mathcal H)\le d^\cap_{\mathrm{DS}}(\mathcal H),\qquad d_{\mathrm{pair}}(\mathcal H)\le d^\cap_{\mathrm{DS}}(\mathcal H),\qquad d^\cap_{\mathrm N}(\mathcal H)\le d^\cap_{\mathrm{pack},\gamma}(\mathcal H)\tag{10}$$
--   for every $0<\gamma<1/(\ell+1)$, and the last inequality holds for $d^\cap_{\mathrm{pack},\rho}$ with every $0<\rho\le1$. Moreover, if $V$ is a DS witness on $S$ and $I$ is a nonempty set of coordinates, then $V|_I$ is a DS witness on the corresponding subsequence; and a packed witness restricted to $I$, with all indices of the list kept, is a packed witness on that subsequence.
--
--   The comparisons let upper bounds in terms of the DS-type dimensions imply bounds in terms of the Natarajan-type one, and the projection statements are used for disjoint products (Lemma 10).
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: a nonempty set I of coordinates and the corresponding subsequence → a strictly increasing e : Fin k → Fin n with 0 < k; V|_I = V.image (· ∘ e); the restricted packed witness keeps M and the list, with blocks B ∘ e; reason: Lean convention
--   - reading: "a packed witness" (Definition 7 defines γ-packed witnesses and, for comparisons, ρ-packed ones) → the restriction statement for every coverage parameter 0 < ρ ≤ 1 (which contains every γ of (9)); reason: both kinds of witness the paper defines are covered
--   - encoding: V|_I as a set of patterns → [DecidableEq Y] to form the Finset image; reason: instance argument only
--   - generalization: X and Y nonempty countable sets (§5.1, p. 25) → X Y : Type* arbitrary, with no Countable or Nonempty instance; reason: a combinatorial statement about patterns that never uses countability; on countable nonempty X, Y it is the paper's statement
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 31 (PDF 33), Lemma 9, (10)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_9 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [DecidableEq Y] (H : Set (Hyp X Y))
    (hH : IsClass ℓ H) :
    natDim H ≤ dsDim H ∧ pairDim H ≤ dsDim H ∧
    (∀ γ : ℝ, 0 < γ → γ < 1 / ((ℓ : ℝ) + 1) → natDim H ≤ packDim ℓ γ H) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → natDim H ≤ packDim ℓ ρ H) ∧
    (∀ (n k : ℕ) (S : Fin n → X) (V : Finset (Fin n → Finset Y)) (e : Fin k → Fin n),
      0 < k → StrictMono e → IsDSWitness H S V →
        IsDSWitness H (S ∘ e) (V.image fun v => v ∘ e)) ∧
    (∀ (n k : ℕ) (ρ : ℝ) (S : Fin n → X) (M : ℕ) (v : Fin M → Fin n → Finset Y)
      (B : Fin n → Finset (Finset (Fin M))) (e : Fin k → Fin n),
      0 < ρ → ρ ≤ 1 → 0 < k → StrictMono e → IsPackedWitness ℓ ρ H S M v B →
        IsPackedWitness ℓ ρ H (S ∘ e) M (fun a => v a ∘ e) (B ∘ e)) := by sorry

end MultiCorrectPAC.Demo
