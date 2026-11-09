-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_4_4
-- name    : KnapsackFPRAS.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:27.129301+00:00
-- url     : https://prove2.me/theorems/4f820af1-7c93-4a3d-a294-996f20968583
-- title:
--   Lemma 4.4 — $|\mathcal A|/|\Omega|\le16Ke^{\lambda\delta}nQ_a(\mathcal A)$
-- statement:
--   Let $w$ be weights and $T$ a capacity, let $\lambda\ge0$ be a tilt with $C^\lambda_w\le16n|\Omega|$ (as given by Lemma 3.2), and let $a\in\mathbb R^n$ be any weight vector (such as the rounded weights) with $Z^\lambda_a\le K Z^\lambda_w$ for some $K\ge1$. Let $\delta\ge0$ and let $\mathcal A\subseteq\Omega$ be a family with $a(I)\le T+\delta$ for every $I\in\mathcal A$. Then
--
--   $$
--   \frac{|\mathcal A|}{|\Omega|}\le16K\,e^{\lambda\delta}\,n\,Q^\lambda_a(\mathcal A).
--   $$
--
--   This converts a small probability under the rounded tilted distribution into a small fraction of the feasible subsets, which is how losses of the construction are counted.
--
--   Differences from the source:
--   - generalization: λ the tilt of Lemma 3.2, a the rounded weights, under (7) → any λ ≥ 0 with C^λ_w ≤ 16n|Ω|, any real vector a, without (7); reason: the proof uses only C^λ_w ≤ 16n|Ω| and λ ≥ 0; the paper's λ and a are such
--   - encoding: |A|/|Ω| → a real division with |Ω| ≥ 1; reason: the empty set is feasible; no junk value
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 4.4, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_KnapsackFPRAS_feasible
import Definitions.Def_KnapsackFPRAS_Tilt

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Lemma 4.4**, p.17. "Suppose that 𝑍_𝑎 ≤ 𝐾𝑍_𝑤 for some 𝐾 ≥ 1. Let 𝛿 ≥ 0, and let A ⊆ Ω
satisfy 𝑎(𝐼) ≤ 𝑇 + 𝛿 for every 𝐼 ∈ A. Then |A|/|Ω| ≤ 16𝐾𝑒^{𝜆𝛿}𝑛𝑄_𝑎(A)."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 4.4, p.17 (PDF p.18).

**Formalization Note.** For every weight vector `w`, capacity `T` and real vector `a` (the
rounded weights are one), and every tilt `λ ≥ 0` with `C^λ_w ≤ 16n|Ω|` (the guarantee of
Lemma 3.2 that the proof uses). `Q_a(A) = ∑_{I∈A} e^{−λa(I)}/Z_a`. The division by `|Ω| ≥ 1`
is a real division. -/
theorem lemma_4_4 {n : ℕ} (w : Fin n → ℕ) (T : ℕ) (a : Fin n → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hC : Tilt.Cnorm (fun i => (w i : ℝ)) lam T ≤ 16 * n * (feasible w T).card)
    (K : ℝ) (hK : 1 ≤ K) (hZ : Tilt.Z a lam ≤ K * Tilt.Z (fun i => (w i : ℝ)) lam)
    (δ : ℝ) (hδ : 0 ≤ δ) (𝒜 : Finset (Finset (Fin n))) (h𝒜 : 𝒜 ⊆ feasible w T)
    (h𝒜a : ∀ I ∈ 𝒜, ∑ i ∈ I, a i ≤ T + δ) :
    (𝒜.card : ℝ) / (feasible w T).card ≤ 16 * K * Real.exp (lam * δ) * n * Tilt.QFam a lam 𝒜 := by sorry

end KnapsackFPRAS
