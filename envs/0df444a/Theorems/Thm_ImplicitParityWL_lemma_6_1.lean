-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_6_1
-- name    : ImplicitParityWL.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:08.866318+00:00
-- url     : https://prove2.me/theorems/42780828-c103-4b31-b731-43fc007124f4
-- title:
--   Lemma 6.1 — counter representation size
-- statement:
--   Let $k\ge3$ and $\ell\ge1$, and suppose $\mathcal I^{k,\ell}_{\mathrm{ctr}}=(W,\mathfrak c,(\mathfrak c_v)_{v\in W},\mathcal E,\iota)$. Then
--   $$
--   \sum_{v\in W}|\mathfrak c_v|+\sum_{e\in\mathcal E}\bigl(|\mathfrak c_e|+2^{\mathrm{rank}\,B_e}\bigr)=O_k(2^\ell).
--   $$
--   With the vertex count (11) of the compiler, this bounds the compiled graphs by $O_k(2^\ell)$ vertices, although the conflict round is of order $2^{(k-1)\ell}$.
--
--   **Formalization Note** The constant depends on $k$ alone, and the rank is that of the restricted check matrix over $\mathbb F_2$.
--
--   Differences from the source:
--   - encoding: = O_k(2^ℓ) → ∃ C : ℕ, chosen before ℓ, sum ≤ C * 2 ^ ℓ; reason: a natural constant loses nothing against a real one
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 6.1, p.34

import Mathlib
import Definitions.Def_ImplicitParityWL_Counter
import Definitions.Def_ImplicitParityWL_CheckMatrix

namespace ImplicitParityWL

/-- **Lemma 6.1** (Counter representation size; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.34): for `k ≥ 3` and `ℓ ≥ 1`, with `ℐ_ctr^{k,ℓ} = (W, 𝔠, (𝔠_v), E, ι)`,
`∑_{v∈W} |𝔠_v| + ∑_{e∈E} (|𝔠_e| + 2^{rank B_e}) = O_k(2^ℓ)`.

**Formalization Note** The constant `C` depends on `k` alone: it is chosen before `ℓ`. The rank is `Matrix.rank` over `𝔽₂`
of the restricted check matrix; deleting zero rows does not change it. -/
theorem lemma_6_1 (k : ℕ) (hk : 3 ≤ k) : ∃ C : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∑ v : CounterLoc ((k - 1) * ℓ), ((counter k ℓ).dom v).card +
      ∑ e : CounterSchema ((k - 1) * ℓ),
        (((counter k ℓ).schema e).dom.card +
          2 ^ (restrictedCheck ((counter k ℓ).schema e).dom).rank) ≤ C * 2 ^ ℓ := by sorry

end ImplicitParityWL
