-- Prove2me | Theorems.Thm_FullHolant_Supplement_theorem_F_A_9
-- name    : FullHolant.Supplement.theorem_F_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:09:45.931235+00:00
-- url     : https://prove2.me/theorems/43017ec9-757d-4cba-bf5d-2de43bcf64fd
-- title:
--   Theorem F.A.9 — affine-plane coefficients
-- statement:
--   Identify $V=\mathbb F_2^3$. Let $c_S\in\mathbb C$ for $S\in\binom V4$, and $\lambda_{pq}\in\mathbb C^\times$ for every unordered pair $\{p,q\}\in\binom V2$. Suppose that whenever $p\in S$, $q\notin S$, $h=p+q$ and $S'=S\triangle\{p,q\}$,
--   $$c_S+c_{S'}=\begin{cases}\lambda_{pq},&\bigoplus_{s\in S}s\in\{0,h\},\\0,&\bigoplus_{s\in S}s\notin\{0,h\}.\end{cases}$$
--   Then there is one $c\in\mathbb C^\times$ such that
--   $$c_S=\begin{cases}c,&\bigoplus_{s\in S}s=0,\\0,&\bigoplus_{s\in S}s\neq0.\end{cases}$$
--   Equivalently, the support consists exactly of the fourteen affine planes of $\mathbb F_2^3$, and all supported coefficients are equal.
--
--   This determines the central coefficients in the height-four analysis (Lemma F.9.10).
--
--   **Formalization Note** $\mathbb F_2^3$ is `Fin 3 → ZMod 2`, so $\bigoplus$ is the sum. The "equivalently" clause is stated too: a four-set has nonzero coefficient iff it is a two-dimensional affine subspace.
--
--   Differences from the source:
--   - encoding: c_S for S ∈ (V choose 4); λ_pq for unordered pairs → `c : Finset V → ℂ` and `lam : Sym2 V → ℂ`, constrained on four-sets and non-diagonal pairs; reason: values elsewhere are never used
-- source:
--   Liu–Meng–Wang, A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems, arXiv:2610.00081 (held version, sha256 d67958c6…), Theorem F.A.9, p.F-79 (PDF p.97)

import Mathlib

set_option autoImplicit false

namespace FullHolant.Supplement

/-- **Theorem F.A.9 (Affine-plane coefficients).** Identify `V = 𝔽₂³`. Let `c_S ∈ ℂ` for
`S ∈ (V choose 4)`, and `λ_{pq} ∈ ℂ×` for every unordered pair `{p, q} ∈ (V choose 2)`. Suppose
that whenever `p ∈ S`, `q ∉ S`, `h = p + q` and `S′ = S △ {p, q}`,
`c_S + c_{S′} = λ_{pq}` if `⊕_{s ∈ S} s ∈ {0, h}` and `= 0` otherwise. Then there is one
`c ∈ ℂ×` with `c_S = c` if `⊕_{s∈S} s = 0` and `c_S = 0` otherwise. Equivalently, the support
consists exactly of the fourteen affine planes of `𝔽₂³`, and all supported coefficients are equal.
Liu–Meng–Wang, *A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems*,
arXiv:2610.00081 (held version, sha256 d67958c6…), Theorem F.A.9, p.F-79 (PDF p.97).

**Formalization Note.** `𝔽₂³` is `Fin 3 → ZMod 2`, so `⊕` is the sum; `c` is given on all finsets
and `λ` on all of `Sym2 V`, only values on four-sets and on pairs enter. The "equivalently" clause
is stated as well: a four-set has nonzero coefficient iff it is an affine plane (a two-dimensional
affine subspace). -/
theorem theorem_F_A_9 (c : Finset (Fin 3 → ZMod 2) → ℂ) (lam : Sym2 (Fin 3 → ZMod 2) → ℂ)
    (hlam : ∀ p q : Fin 3 → ZMod 2, p ≠ q → lam s(p, q) ≠ 0)
    (hrel : ∀ S : Finset (Fin 3 → ZMod 2), S.card = 4 → ∀ p ∈ S, ∀ q ∉ S,
      c S + c (symmDiff S {p, q}) =
        if (∑ s ∈ S, s = 0 ∨ ∑ s ∈ S, s = p + q) then lam s(p, q) else 0) :
    ∃ c0 : ℂ, c0 ≠ 0 ∧
      (∀ S : Finset (Fin 3 → ZMod 2), S.card = 4 → c S = if ∑ s ∈ S, s = 0 then c0 else 0) ∧
      (∀ S : Finset (Fin 3 → ZMod 2), S.card = 4 →
        (c S ≠ 0 ↔ ∃ E : AffineSubspace (ZMod 2) (Fin 3 → ZMod 2),
          Module.finrank (ZMod 2) E.direction = 2 ∧ (S : Set (Fin 3 → ZMod 2)) = E)) := by sorry

end FullHolant.Supplement
