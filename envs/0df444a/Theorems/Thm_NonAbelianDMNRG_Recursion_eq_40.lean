-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_eq_40
-- name    : NonAbelianDMNRG.Recursion.eq_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:31.047696+00:00
-- url     : https://prove2.me/theorems/1a12c3c3-ceee-49dd-ac32-654cbc626abf
-- title:
--   Eq. (40) — the partial trace over the site intertwines $V\otimes L$ conjugation with $V$ conjugation
-- statement:
--   Let $a$ and $b$ be finite index sets and consider operators on $\mathbb C^a\otimes\mathbb C^b$, where the second factor plays the role of the last NRG site. Write $\operatorname{Tr}_{\mathrm{site}}$ for the partial trace over the second factor. For every matrix $V$ on $\mathbb C^a$, every unitary matrix $L$ on $\mathbb C^b$ (that is, $L^\dagger L = 1$) and every operator $R$ on $\mathbb C^a\otimes\mathbb C^b$,
--   $$
--   \operatorname{Tr}_{\mathrm{site}}\big\{(V\otimes L)\, R\, (V\otimes L)^\dagger\big\} = V\, \operatorname{Tr}_{\mathrm{site}}\{R\}\, V^\dagger .
--   $$
--
--   In the paper the symmetry transformation on the first $n$ sites factors as $U(g) = L(g)V(g)$, with $L(g)$ acting on site $n$ and $V(g)$ on sites $0,\dots,n-1$; this identity is the step that moves the symmetry through the trace over site $n$.
--
--   **Formalization Note** The statement holds for an arbitrary $V$; only $L$ needs to be unitary. Operators are indexed with the block factor first and the site factor second; the partial trace is the published `WildeQIT.partialTraceRight`.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, eq. (40)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **Eq. (40), p. 7.** Tracing out the right factor (the site) intertwines conjugation by
`V ⊗ L` with conjugation by `V`, for any `V` and any unitary `L`:
`Tr_site{(V ⊗ L) R (V ⊗ L)⁺} = V Tr_site{R} V⁺`. -/
theorem eq_40 {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a a ℂ) (L : Matrix b b ℂ) (hL : Lᴴ * L = 1)
    (R : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight ((V ⊗ₖ L) * R * (V ⊗ₖ L)ᴴ) =
      V * WildeQIT.partialTraceRight R * Vᴴ := by sorry

end NonAbelianDMNRG.Recursion
