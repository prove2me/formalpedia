-- Prove2me | Theorems.Thm_NonadaptiveSFT_proposition_8
-- name    : NonadaptiveSFT.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:34.648368+00:00
-- url     : https://prove2.me/theorems/33cb963a-0e4d-4d73-93b6-004ed39daed5
-- title:
--   Proposition 8 — the projection onto $v+H_j$ is a character-weighted average over the annihilator: $h_{v,j,R}(t)=\mathbb E_{z\in K_j}R(t+z)\overline{\chi_v(z)}$
-- statement:
--   Let $a,d\ge1$. For every $v\in G$, every depth $0\le j\le ad$, every signal $R:G\to\mathbb C$ and every $t\in G$,
--
--   $$h_{v,j,R}(t)=\mathbb E_{z\in K_j}\,R(t+z)\,\overline{\chi_v(z)},\tag{12}$$
--
--   where $K_j=\{z\in G:\chi_h(z)=1\ \forall h\in H_j\}$ is the annihilator of $H_j$. For $j=\ell a+c<ad$ with $0\le c<a$,
--
--   $$K_j=(\mathbb Z/2^a\mathbb Z)^\ell\times(2^{a-c}\mathbb Z/2^a\mathbb Z)\times\{0\}^{d-\ell-1},$$
--
--   and $K_{ad}=G$.
--
--   This identity is what makes the frequency tree searchable with point queries: the node statistic at $v+H_j$ is an average of values of $R$ on a coset of $K_j$.
--
--   Differences from the source:
--   - encoding: coordinates 1, …, d → indices 0, …, d − 1 (coordinate ℓ + 1 is index ℓ); reason: Lean's Fin d; same sets
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Proposition 8 and eq. (12), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Subgroups

namespace NonadaptiveSFT

/-- **Proposition 8**, p.21 (PDF p.23).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

For any `v ∈ G`, `0 ≤ j ≤ log N = ad` and `R : G → ℂ`,
`h_{v,j,R}(t) = E_{z∈K_j} R(t+z)·conj(χ_v(z))` (12), where `K_j` is the annihilator of `H_j`. For
`j = ℓa + c < ad` it is `(ℤ/2^aℤ)^ℓ × (2^{a−c}ℤ/2^aℤ) × {0}^{d−ℓ−1}`, and `K_ad = G`.

**Formalization Note.** `K_j` is defined as the annihilator (`NonadaptiveSFT.Kann`), and its product
form is the second clause; `ℓ = j / a`, `c = j % a`, the paper's coordinate `ℓ + 1` is the index `ℓ`,
coordinates `1, …, ℓ` (unconstrained) are the indices `i < ℓ`. `E_{z∈K_j}` is the average over the
finite set `K_j`. -/
theorem proposition_8 (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    (∀ (v : G a d) (j : ℕ), j ≤ a * d → ∀ (R : G a d → ℂ) (t : G a d),
      hproj v j R t =
        (1 / ((Kann a d j).card : ℂ)) * ∑ z ∈ Kann a d j, R (t + z) * (starRingEnd ℂ) (chi v z)) ∧
    (∀ j : ℕ, j < a * d → ∀ z : G a d,
      z ∈ Kann a d j ↔ ∀ i : Fin d,
        ((i : ℕ) = j / a → ∃ m : ZMod (2 ^ a), z i = 2 ^ (a - j % a) * m) ∧
        (j / a < (i : ℕ) → z i = 0)) ∧
    Kann a d (a * d) = Finset.univ := by sorry

end NonadaptiveSFT
