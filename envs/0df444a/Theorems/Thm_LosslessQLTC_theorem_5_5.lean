-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_5_5
-- name    : LosslessQLTC.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:02.190945+00:00
-- url     : https://prove2.me/theorems/87e5899c-f0a3-410a-a43c-da567bb31b42
-- title:
--   Theorem 5.5, p.42 — a two-sided lossless imbalanced $(4,2)$-cubical complex gives a good quantum locally testable code
-- statement:
--   There is an absolute constant $\varepsilon_0>0$ with the following property. Let $D,D':[4]\to\mathbb N$ and $c,\varepsilon:[4]\to\mathbb R$ with $\varepsilon_\star=\sum_j\varepsilon_j<\varepsilon_0$, let $\mu_i=D_i/D'_i$ satisfy $\mu_1,\mu_2\ge4$ and $\mu_3,\mu_4\le1/4$, and write
--
--   $$c_0=\frac{\min_jc_j}{2^4\,4!\,D'_{[4]}D_{[4]}}.$$
--
--   Let $X$ be a $(4,2)$-cubical complex with these degrees, such that $X$ and $X^{\mathrm{rev}}$ are both lossless with parameters $c,\varepsilon$ and both satisfy the imbalance (4.25). Then $C(\ker\delta_1^t,\ker\delta_2)$, with qubits on $V_2$, satisfies:
--
--   1. (CSS.) $\operatorname{im}\delta_1\le\ker\delta_2$.
--   2. (Rate.) $\dim(\ker\delta_2/\operatorname{im}\delta_1)/|V_2|>1/10$.
--   3. (Relative distance.) Every $w\in\ker\delta_2\setminus\operatorname{im}\delta_1$ has $\|w\|_X\ge c_0\|V_2\|_X$ and $|w|\ge c_0|V_2|/D_{[4]}$. Every $w\in\ker\delta_1^t\setminus\operatorname{im}\delta_2^t$ has $\|w\|_{X^{\mathrm{rev}}}\ge c_0\|V_2\|_{X^{\mathrm{rev}}}$ and $|w|\ge c_0|V_2|/D'_{[4]}$.
--   4. (Local testability soundness.) For every word $w\in C^2(X)$,
--
--   $$\|\delta_2w\|_X\ge s_Z\operatorname{dist}_X(w,\ker\delta_2),\qquad\|\delta_1^tw\|_{X^{\mathrm{rev}}}\ge s_X\operatorname{dist}_{X^{\mathrm{rev}}}(w,\ker\delta_1^t),$$
--
--   with $s_Z=\min\{c_0\beta,1/(6D_{[4]})\}$, $s_X=\min\{c_0\beta^{\mathrm{rev}},1/(6D'_{[4]})\}$, $\beta=\|V_3\|_X/\|V_2\|_X$ and $\beta^{\mathrm{rev}}=\|V_1\|_{X^{\mathrm{rev}}}/\|V_2\|_{X^{\mathrm{rev}}}$, both functions of the degrees alone.
--   5. (Locality.) Every row of $\delta_2$ has weight at most $3\max_iD'_i$, every row of $\delta_1^t$ has weight at most $3\max_iD_i$, and every column of each has weight at most $\sum_i(D_i+D'_i)$.
--
--   All constants depend only on $D,D',c$ and precede $X$, so the theorem applies uniformly to every finite complex with these parameters. The theorem is conditional: complexes of unbounded size with these properties are not known to exist.
--
--   Differences from the source:
--   - generalization: constant rate, relative distance and local testability soundness → the explicit constants of the proof: rate above $1/10$, distance $c_0$ in norm and $c_0/D_{[4]}$, $c_0/D'_{[4]}$ relatively, $s_Z,s_X$, and the row and column bounds of p.42; reason: these are functions of $D,D',c$ fixed before $X$, so they imply the existential form
--   - reading: $\varepsilon_\star$ sufficiently small (footnote 7: so that the inequality in Theorem 4.10 is meaningful) → $\varepsilon_\star<\varepsilon_0$ for an absolute $\varepsilon_0>0$ chosen before all parameters; reason: the $O_4$ constants of Theorem 4.10 depend only on $k=4$, and footnote 7 ties smallness only to that inequality
--   - reading: constant → uniform in $X$: quantified over $D,D',c,\varepsilon$ first and every $X$ with these parameters after; reason: p.39 fixes the degree and lossless parameters independently of the code length; a constant depending on the finite $X$ would be empty
--   - reading: $X$ and $X^{\mathrm{rev}}$ satisfy the assumptions of Theorem 4.10 → lossless with $(c,\varepsilon)$ and (4.25) for each of $X$, $X^{\mathrm{rev}}$; the range condition on $H_r$ is a hypothesis of Theorem 4.10 on the cochain, not on $X$; reason: (4.25) for $X^{\mathrm{rev}}$ is $\varepsilon_tD_s\le\varepsilon_\star$ with the same order $s<t$
--   - encoding: $\mu_i\ge4$, $\mu_i\le1/4$ with $\mu_i=D_i/D'_i$ and directions $1,\dots,4$ → real ratios `D i / D' i` with directions `0,…,3` of `Fin 4`; reason: the order of directions is kept; $D'_i>0$
--   - encoding: $\delta_1^t$, $\delta_2^t$ → `partialMap X 1`, `partialMap X 2`; reason: these are the transposes, with the index giving the target level
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 5.5, p.42; constants from its proof, pp.42–43, and eq. (4.26), p.37

import Mathlib
import Definitions.Def_LosslessQLTC_IsLossless
import Definitions.Def_LosslessQLTC_codeDim
import Definitions.Def_LosslessQLTC_betaConst

namespace LosslessQLTC

/-- Theorem 5.5 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.42): let `X` be a
`(4, 2)`-cubical complex such that `X` and `X^rev` satisfy the assumptions of Theorem 4.10, with `ε⋆`
sufficiently small and with stretch/shrinkage factors `µ_1, µ_2 ≥ 4` and `µ_3, µ_4 ≤ 1/4`. Then
`C(ker δ_1^t, ker δ_2)` is a quantum error-correcting code with constant rate, relative distance and
local testability soundness.

**Formalization Note.** `ε₀` is absolute (footnote 7), and it precedes all parameters. The constants
are the explicit ones of the proof, pp.42–43, as functions of `D, D′, c`, so they precede `X`:
`c₀ = cConst D D' c` of (4.26), rate above `1/10`, `∥w∥ ≥ c₀ ∥V_2∥`, `s_Z = min{c₀ β, 1/(6 D_{[4]})}`,
`s_X = min{c₀ β^rev, 1/(6 D′_{[4]})}`, and the row and column bounds of p.42. The Hamming bound on
`w` is the norm bound together with Remark 2.11. Directions `1, …, 4` are `Fin 4`, so `µ_1` is
`D 0 / D' 0`. `H_Z = δ_2` is `delta X 2`, and `H_X = δ_1^t` is `partialMap X 1`, with
`im δ_2^t = range (partialMap X 2)`. The X-code carries the reversed norm (p.40). -/
theorem theorem_5_5 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (D D' : Fin 4 → ℕ) (c ε : Fin 4 → ℝ),
        epsStar ε < ε₀ →
        (4 : ℝ) ≤ (D 0 : ℝ) / D' 0 → (4 : ℝ) ≤ (D 1 : ℝ) / D' 1 →
        (D 2 : ℝ) / D' 2 ≤ 1 / 4 → (D 3 : ℝ) / D' 3 ≤ 1 / 4 →
        ∀ X : SquareComplex 4, X.D = D → X.D' = D' →
          IsTwoSidedLossless X c ε → IsImbalanced X ε → IsImbalanced (rev X) ε →
          -- the CSS condition `C_X^⊥ ≤ C_Z`
          LinearMap.range (delta X 1) ≤ LinearMap.ker (delta X 2) ∧
          -- rate
          (1 : ℝ) / 10 < (codeDim X : ℝ) / Fintype.card (Level X 2) ∧
          -- relative distance
          (∀ w : Level X 2 → ZMod 2, w ∈ LinearMap.ker (delta X 2) →
            w ∉ LinearMap.range (delta X 1) →
            cConst D D' c * levelMass X 2 ≤ normC X w ∧
            cConst D D' c * (Fintype.card (Level X 2) : ℝ) / (prodD D Finset.univ : ℝ) ≤
              (hammingNorm w : ℝ)) ∧
          (∀ w : Level X 2 → ZMod 2, w ∈ LinearMap.ker (partialMap X 1) →
            w ∉ LinearMap.range (partialMap X 2) →
            cConst D D' c * levelMassRev X 2 ≤ normRev X w ∧
            cConst D D' c * (Fintype.card (Level X 2) : ℝ) / (prodD D' Finset.univ : ℝ) ≤
              (hammingNorm w : ℝ)) ∧
          -- local testability soundness, for every word
          (∀ w : Level X 2 → ZMod 2,
            min (cConst D D' c * betaConst D') (1 / (6 * (prodD D Finset.univ : ℝ))) *
                distTo (normC X) (LinearMap.ker (delta X 2)) w ≤
              normC X (delta X 2 w)) ∧
          (∀ w : Level X 2 → ZMod 2,
            min (cConst D D' c * betaConst D) (1 / (6 * (prodD D' Finset.univ : ℝ))) *
                distTo (normRev X) (LinearMap.ker (partialMap X 1)) w ≤
              normRev X (partialMap X 1 w)) ∧
          -- locality: row weights
          (∀ w : Level X 3,
            (((Finset.univ : Finset (Level X 2)).filter fun v => X.up v.1 w.1).card) ≤
              3 * Finset.univ.sup D') ∧
          (∀ u : Level X 1,
            (((Finset.univ : Finset (Level X 2)).filter fun v => X.up u.1 v.1).card) ≤
              3 * Finset.univ.sup D) ∧
          -- locality: column weights
          (∀ v : Level X 2,
            (((Finset.univ : Finset (Level X 3)).filter fun w => X.up v.1 w.1).card) ≤
              ∑ i, (D i + D' i)) ∧
          (∀ v : Level X 2,
            (((Finset.univ : Finset (Level X 1)).filter fun u => X.up u.1 v.1).card) ≤
              ∑ i, (D i + D' i)) := by sorry

end LosslessQLTC
