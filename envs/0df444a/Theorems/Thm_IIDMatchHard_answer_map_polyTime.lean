-- Prove2me | Theorems.Thm_IIDMatchHard_answer_map_polyTime
-- name    : IIDMatchHard.answer_map_polyTime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:08:09.470008+00:00
-- url     : https://prove2.me/theorems/d5ef10e3-b4f8-40c4-bc7f-6b71ceeab3e0
-- title:
--   Proof of Theorem 3.1, p.23 — the answer map $\bar V\mapsto\bar C$ is polynomial-time
-- statement:
--   Fix a rational $c>0$ and an integer $B\ge1$, and put $\lambda=c/B$. Some polynomial-time machine reads a graph $G$ and a rational number $\bar V$ and outputs a rational number $\bar C$ with
--   $$\big|\Phi_{\tilde G}(B^2\bar C)-\bar V\big|\ \le\ 1,$$
--   where $\Phi_{\tilde G}$ is the affine function of Lemma 3.6 for the blow-up $\tilde G$ of $G$ at $\lambda=c/B$.
--
--   This is the answer map of the reduction: it inverts the affine map $x\mapsto\Phi_{\tilde G}(B^2x)$, whose coefficients involve $e$, up to an additive error of $1$.
--
--   Differences from the source:
--   - reading: "We output a rational number C̄ … As c and B are constants, the algorithm runs in polynomial time" → a Cook machine reading encGraph H, a separator and encRat V̄, and writing encRat C̄, for every graph and every rational V̄; reason: the input and output are the binary encodings
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), proof of Theorem 3.1, App. B.9, p.23 (PDF p.24)

import Definitions.Def_IIDMatchHard_Reduction
import Definitions.Def_IIDMatchHard_Adjusted
import Definitions.Def_IIDMatchHard_ApproxNPHard

set_option autoImplicit false

open NSWApxHard.Reduction

namespace IIDMatchHard

/-- **The answer map of the reduction** (proof of Theorem 3.1). For a rational `c > 0` and an
integer `B ≥ 1`, with `λ = c/B`, some polynomial-time machine reads a graph `G` and a rational
`V̄` and outputs a rational `C̄` with `|Φ_G̃(B²C̄) − V̄| ≤ 1`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), proof of Theorem 3.1, p.23
(PDF p.24): "We output a rational number C̄ with |Φ_G̃(B²C̄) − V̄| ≤ 1, which we compute from a
rational approximation of e. As c and B are constants, the algorithm runs in polynomial time."

**Formalization Note.** The machine reads `encGraph H`, a separator and `encRat V̄`
(`pairInput`), and writes `encRat C̄`. `Φ_G̃` is `Φ` of `G̃ = blowUp G B` at `λ = c/B`. It works
for every graph and every rational `V̄`. -/
theorem answer_map_polyTime (c : ℚ) (hc : 0 < c) (B : ℕ) (hB : 1 ≤ B) :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ (H : GraphInput) (q : ℚ), ∃ C : ℚ, g (pairInput (encGraph H) q) = ImpatientMatching.encRat C ∧
        |Phi (blowUp H.G B) ((c : ℝ) / B) ((B : ℝ) ^ 2 * (C : ℝ)) - (q : ℝ)| ≤ 1 := by sorry

end IIDMatchHard
