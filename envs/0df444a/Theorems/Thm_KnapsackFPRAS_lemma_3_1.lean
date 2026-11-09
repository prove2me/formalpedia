-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_3_1
-- name    : KnapsackFPRAS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:55.732662+00:00
-- url     : https://prove2.me/theorems/b5ebd7e0-054e-4e48-9532-6cde02a815be
-- title:
--   Lemma 3.1 — $|\Omega|\le\min_{\lambda\ge0}C^\lambda_w\le4n|\Omega|$
-- statement:
--   Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)). For $\lambda\ge0$ let $C^\lambda_w=e^{\lambda T}\prod_{i=1}^n(1+e^{-\lambda w_i})$. Then the minimum of $C^\lambda_w$ over $\lambda\ge0$ is attained, and
--
--   $$
--   |\Omega|\le\min_{\lambda\ge0}C^\lambda_w\le4n|\Omega| .
--   $$
--
--   Since every feasible subset has probability at least $1/C^\lambda_w$ under the tilted distribution, a tilt with $C^\lambda_w=O(n|\Omega|)$ turns a small loss of tilted probability into a small loss of feasible subsets. This lemma shows such a tilt exists.
--
--   Differences from the source:
--   - reading: min_{λ≥0} C^λ_w (attainment implicit) → ∃ λ₀ ≥ 0 with C^{λ₀}_w ≤ C^λ_w for all λ ≥ 0 and |Ω| ≤ C^{λ₀}_w ≤ 4n|Ω|; reason: the page writes the minimum, so it asserts that it is attained; C^λ_w is continuous and tends to ∞
--   - encoding: [n] → Fin n; reason: index shift; same instances
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 3.1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_KnapsackFPRAS_feasible
import Definitions.Def_KnapsackFPRAS_Tilt

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Lemma 3.1**, p.11. "Under the assumptions in (7), we have |Ω| ≤ min_{𝜆≥0} 𝐶^𝜆_𝑤 ≤ 4𝑛|Ω|."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 3.1, p.11 (PDF p.12).

**Formalization Note.** The minimum is stated as its existence and its two bounds: there is
`λ₀ ≥ 0` with `C^{λ₀}_w ≤ C^λ_w` for every `λ ≥ 0`, and `|Ω| ≤ C^{λ₀}_w ≤ 4n|Ω|`. Here
`C^λ_w = e^{λT} ∏ᵢ (1 + e^{−λwᵢ})`. -/
theorem lemma_3_1 {n : ℕ} (w : Fin n → ℕ) (T : ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ T) (hsum : T < ∑ i, w i) :
    ∃ lam₀ : ℝ, 0 ≤ lam₀ ∧
      (∀ lam : ℝ, 0 ≤ lam → Tilt.Cnorm (fun i => (w i : ℝ)) lam₀ T ≤
        Tilt.Cnorm (fun i => (w i : ℝ)) lam T) ∧
      ((feasible w T).card : ℝ) ≤ Tilt.Cnorm (fun i => (w i : ℝ)) lam₀ T ∧
      Tilt.Cnorm (fun i => (w i : ℝ)) lam₀ T ≤ 4 * n * (feasible w T).card := by sorry

end KnapsackFPRAS
