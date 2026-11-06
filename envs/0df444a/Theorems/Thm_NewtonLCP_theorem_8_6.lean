-- Prove2me | Theorems.Thm_NewtonLCP_theorem_8_6
-- name    : NewtonLCP.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:57.664366+00:00
-- url     : https://prove2.me/theorems/c9a3756c-44be-483d-9920-4b8003e9e8b5
-- title:
--   Theorem 8.6 — $\hat\kappa(M)<2^{O(n\,\mathrm{length}(M))}$ for rational $\mathcal P_\star$-matrices
-- statement:
--   For every $M\in\mathcal P_\star\cap\mathbb Q^{n\times n}$ with encoding length $\mathrm{length}(M)$,
--
--   $$\hat\kappa(M)<2^{O(n\,\mathrm{length}(M))}.$$
--
--   This result of E.-Nagy and Végh [ENV26], cited in the paper, bounds the number of doublings of the guess $\kappa$ in Algorithm 3.
--
--   **Formalization Note** $2^{O(n\,\mathrm{length}(M))}$ is $2^{C\,n\,\mathrm{length}(M)}$ with one constant $C$ for all $n$ and $M$.
--
--   Differences from the source:
--   - encoding: κ̂(M) < 2^{O(n length(M))} → ∃ C : ℕ before all n, M with κ̂(M) < 2^{C·n·length(M)}; reason: O(·) is one constant uniform in the instance; n·length(M) ≥ 2 whenever n ≥ 1, so a multiplicative constant absorbs additive ones
--   - encoding: length(M) → Σ bitSize of the entries of M; reason: any standard encoding is within constant factors
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 8.6, p.31 (cited)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Encoding

namespace NewtonLCP

/-- **Theorem 8.6** ([ENV26]). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 8.6, p.31 (cited; not proved in the paper).

For any `M ∈ P⋆ ∩ ℚⁿˣⁿ` with encoding length `length(M)`, `κ̂(M) < 2^{O(n length(M))}`.

**Formalization Note.** `2^{O(n length(M))}` is `2^{C·n·length(M)}` with one constant `C` for all
`n` and `M` (chosen before them); `length(M) = encLenM M`. -/
theorem theorem_8_6 : ∃ C : ℕ, ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
    IsPStar (M.map ((↑) : ℚ → ℝ)) →
      handicap (M.map ((↑) : ℚ → ℝ)) < 2 ^ (C * n * encLenM M) := by sorry

end NewtonLCP
