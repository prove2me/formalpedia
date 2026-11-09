-- Prove2me | Theorems.Thm_NadlerCLS_lemma_C_1_circuit
-- name    : NadlerCLS.lemma_C_1_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:36.114483+00:00
-- url     : https://prove2.me/theorems/fdf80386-dc85-49e6-ad38-3e627857c067
-- title:
--   Lemma C.1 (i), computational part — polynomial-time construction of the interpolant circuit, vertices and weights (companion: lemma_C_1)
-- statement:
--   1. There is a polynomial-time algorithm that, given $n$, $r$, $m\ge1$ and a well-behaved circuit $g$ with $n$ inputs and $r$ outputs, outputs a well-behaved circuit $G$ with $n$ inputs and $r$ outputs such that, for every $x\in[0,1]^n$,
--   $$ G(x)=I_hg(x),\qquad h=2^{-m}, $$
--   the simplex-based interpolant of $g$ (with $g$'s values clipped to $[0,1]^r$).
--   2. There is a polynomial-time algorithm that, given $n$, $m\ge1$ and a rational point $x\in[0,1]^n$, outputs the $n+1$ vertices and the $n+1$ weights selected at $x$, as rational numbers.
--
--   The circuit computes only the simplex selected by its input, so its size is polynomial in $n,r,m$ and the size of $g$, not in the $2^{mn}$ grid cubes; this is what makes the reduction of Theorem C.2 polynomial.
--
--   Differences from the source:
--   - encoding: time polynomial in $n$, $r$, $m$ and the description length of $g$ → `CookPvsNP.PolyTimeComputable` maps whose input lists $n$, $r$, $m$ in unary before the code of $g$ (resp. of $x$); reason: polynomial in the unary lengths is polynomial in $n$, $r$, $m$
--   - encoding: $g:[0,1]^n\to[0,1]^r$ → the interpolant of $g$'s outputs clipped to $[0,1]$; equality on the cube; reason: the stated range; clipping leaves in-range circuits unchanged
--   - encoding: vertices and weights computable → rational vertices and weights coded with `encList encVector` and `encVector`; reason: p.7's rational binary data
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Lemma C.1, p.31, and "Polynomial-time circuit construction", pp.33–34

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_NadlerCLS_kuhnInterp

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **Lemma C.1: polynomial-time construction of the interpolant circuit, and of its vertices and
weights** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Lemma C.1,
p.31: "One can construct a well-behaved circuit Ihg : [0, 1]n → [0, 1]r, in time polynomial in n, r,
m and the description length of g … These vertices and weights are computable within the same
bound"; construction on pp.33–34).

1. There is a polynomial-time map `interp` that, given `n`, `r`, `m ≥ 1` (in unary) and a valid
   well-behaved circuit `g` with `n` inputs and `r` outputs, returns a valid well-behaved circuit `G`
   with `n` inputs and `r` outputs whose output on every `x ∈ [0, 1]ⁿ` is `I_h g(x)`, the
   interpolant of the clipped `g` on the grid of length `h = 2^{−m}`.
2. There is a polynomial-time map `vw` that, given `n`, `m ≥ 1` (in unary) and a rational point
   `x ∈ [0, 1]ⁿ`, returns the `n + 1` selected vertices and the `n + 1` weights at `x`, as rationals.

**Formalization Note** Polynomial time is the public `CookPvsNP.PolyTimeComputable` in the input
length; `n`, `r`, `m` are written in unary (`List.replicate k true ++ [false]`) so that "polynomial
in n, r, m" is polynomial in the input length. `g`'s outputs are clipped to `[0, 1]`, the range
`g : [0, 1]ⁿ → [0, 1]ʳ`. -/
theorem lemma_C_1_circuit :
    (∃ interp : List Bool → List Bool, PolyTime interp ∧
      ∀ (n r m : ℕ) (g : Circ), 1 ≤ m → g.Valid n r →
        ∃ G : Circ,
          interp (List.replicate n true ++ false :: List.replicate r true ++
            false :: List.replicate m true ++ false :: encCirc g) = encCirc G ∧
          G.Valid n r ∧
          ∀ x : Fin n → ℝ, InCube x →
            (fun i : Fin r => G.eval x i) =
              kuhnInterp m (fun (v : Fin n → ℝ) (i : Fin r) => clip (g.eval v i)) x) ∧
    (∃ vw : List Bool → List Bool, PolyTime vw ∧
      ∀ (n m : ℕ) (x : Fin n → ℚ), 1 ≤ m → InCube (rpt x) →
        ∃ (V : Fin (n + 1) → Fin n → ℚ) (w : Fin (n + 1) → ℚ),
          vw (List.replicate n true ++ false :: List.replicate m true ++
            false :: encVector x) = encList encVector (List.ofFn V) ++ encVector w ∧
          (∀ j, rpt (V j) = kuhnVertex m (rpt x) j) ∧
          ∀ j, (w j : ℝ) = kuhnWeight m (rpt x) j) := by sorry

end NadlerCLS
