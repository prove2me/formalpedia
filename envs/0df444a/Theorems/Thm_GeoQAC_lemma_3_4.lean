-- Prove2me | Theorems.Thm_GeoQAC_lemma_3_4
-- name    : GeoQAC.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:05.644935+00:00
-- url     : https://prove2.me/theorems/d705ccd7-bfb1-49fa-aba0-f6296afd261e
-- title:
--   Lemma 3.4 — product states have $\Gamma\le1$
-- statement:
--   Let $\Lambda=[w]\times[h]$ be the qubit grid and let $\Gamma$ be the local measurement variance. Every product state $\rho=\bigotimes_{v\in\Lambda}\rho_v$ satisfies
--   $$
--   \Gamma(\rho)\le 1 .
--   $$
--
--   This is the base case of the potential argument: a circuit's input state has bounded $\Gamma$.
--
--   Differences from the source: none.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.4, p.14

import Mathlib
import Definitions.Def_GeoQAC_lmv
import Definitions.Def_GeoQAC_IsProductState

namespace GeoQAC

/-- **Lemma 3.4** (arXiv:2604.07178, version of 2026-11-03, p.14). Every product state
`ρ = ⊗_{v∈Λ} ρ_v` on the grid `Λ = [w] × [h]` satisfies `Γ(ρ) ≤ 1`.

**Formalization Note.** `ρ_v` are arbitrary (possibly mixed) one-qubit states; `Γ` is `lmv`, the
supremum of Definition 3.2 with the L2 operator norm. -/
theorem lemma_3_4 {w h : ℕ} (ρ : Matrix (Pos w h → Bool) (Pos w h → Bool) ℂ)
    (hρ : IsProductState ρ) : lmv ρ ≤ 1 := by sorry

end GeoQAC
