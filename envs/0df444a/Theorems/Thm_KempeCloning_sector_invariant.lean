-- Prove2me | Theorems.Thm_KempeCloning_sector_invariant
-- name    : KempeCloning.sector_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:22.536921+00:00
-- url     : https://prove2.me/theorems/08ceb676-e2bb-45d5-8431-9e55d54fbab2
-- title:
--   Eq. (15): the sector states are closed under $\mathcal H$
-- statement:
--   Let $\gamma\in\mathbb R$, $m,N\in\mathbb N$, and let $\mathcal H$ be the Hamiltonian (14). For every pair $(i,j)$ with $i+j\le N$, every number state that occurs with nonzero amplitude in
--
--   $$\mathcal H\,\big|(m+j)_{a_1}, i_{a_2}, i_{b_1}, j_{b_2}, (N-i-j)_c\big\rangle$$
--
--   is again of the form $|(m+j')_{a_1}, i'_{a_2}, i'_{b_1}, j'_{b_2}, (N-i'-j')_c\rangle$ with $i'+j'\le N$.
--
--   Consequently the span of the states (15) is a finite-dimensional subspace that contains the initial state $|m,0,0,0,N\rangle$ (the case $i=j=0$) and is invariant under $\mathcal H$; this is what makes the evolution $e^{-i\mathcal Ht}$ of the paper a finite-dimensional matrix exponential.
--
--   Differences from the source:
--   - generalization: "Action of (14) on (13) generates Fock basis states of the general form (15)" → every state of the form (15) is mapped by $\mathcal H$ into superpositions of states of the form (15); reason: closure of the whole family under $\mathcal H$ implies, by induction on the power of $\mathcal H$, that everything generated from (13), the case $i=j=0$, is of the form (15)
--   - encoding: $= |m+j, i\rangle_{photons}|i, j, N-i-j\rangle_{atoms}$ → not stated; reason: a relabelling of the same Fock state in the notation of the Schwinger representation; it has no content inside the oscillator model (13)–(14)
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
--   - reading: coupling constant $\gamma$, whose type the page does not state → $\gamma\in\mathbb R$; reason: (21) is printed with the same $\gamma$ on the term from (14) and on its h.c., which holds only for real $\gamma$, and the page absorbs phases into $\gamma$ (p.4)
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4

import Definitions.Def_KempeCloning_ham
import Definitions.Def_KempeCloning_sectorIndex

namespace KempeCloning

/-- **The sector (15) is closed under `H` (14).**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4: "Action of (14) on (13)
generates Fock basis states of the general form |(m + j)_{a1}, i_{a2}, i_{b1}, j_{b2}, (N − i − j)_c⟩
= |m + j, i⟩photons|i, j, N − i − j⟩atoms. (15)"

For every real `γ`, all `m, N`, and every label `(i, j)` with `i + j ≤ N`, every Fock basis state
occurring in `H |(m + j), i, i, j, (N − i − j)⟩` is again of the form (15).

**Formalization Note.** Only the Fock-space half of (15) is formalized; the identification with the
symmetric atomic states `|i, j, N − i − j⟩atoms` belongs to the Schwinger representation and is not
part of this mission. -/
theorem sector_invariant (γ : ℝ) (m N : ℕ) (q : Sector N) :
    ∀ n ∈ (ham γ (Finsupp.single (sectorIndex m N q) 1)).support,
      n ∈ Set.range (sectorIndex m N) := by sorry

end KempeCloning
