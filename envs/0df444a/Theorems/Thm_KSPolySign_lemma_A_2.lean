-- Prove2me | Theorems.Thm_KSPolySign_lemma_A_2
-- name    : KSPolySign.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:42:21.804979+00:00
-- url     : https://prove2.me/theorems/c06a10db-1542-4d48-b2dd-76a206d3de9f
-- title:
--   Lemma A.2 — polynomial certificate
-- statement:
--   Let $F_n,B_n,U_n,Q_n,Z_n,P_n$ be the polynomials in $(t,H,V)$ defined in the proof (p.73). Then
--   $$\min\{F_n,B_n,U_n,Z_n,P_n\}>\tfrac1{400}\qquad\text{on }[0,1]^3.\tag{147}$$
--   Let $y$ be a light state and $i$ an active coordinate with $y_i\ge0$; write $z=y_i$, $w=\sqrt{1-z^2}$, $\delta=\delta_i$, $k=k_i$, $s_{\mathrm{inv}}=1/k$. If $(t,H,V)\in[0,1)\times[0,1]^2$ satisfies
--   $$z=\frac{2t}{1+t^2},\quad w=\frac{1-t^2}{1+t^2},\quad \delta=\frac w\iota H,\quad s_{\mathrm{inv}}=\frac{2\eta}\iota w\big(1+z(1-H)(2V-1)\big),\tag{148}$$
--   then, with $g=1+t^2$,
--   $$F=\frac{F_n}{g^2},\quad B=\frac{B_n}{g^2},\quad \mathfrak u=\frac{U_n}{g^5},\quad \mathfrak q=\frac{Q_n}{g^6},\quad \mathfrak z=\frac{Z_n}{g^6}.\tag{149}$$
--
--   Together with Lemma A.1 this certifies Lemma 5.2 by finitely many exact rational computations.
--
--   **Formalization Note** The polynomials are the explicit ones of the proof, as real polynomial functions. The light coordinate is the scalar triple $(y,u,v)$, as in Lemma 5.2.
--
--   Differences from the source:
--   - generalization: there are rational polynomials F_n, …, P_n → the explicit polynomials defined in the proof (p.73); reason: they have rational coefficients, so the statement implies the printed existential one
--   - generalization: an active coordinate i with y_i ≥ 0 of a light state → every scalar triple (y, u, v) with 0 ≤ y < 1, u, v > 0 and the two light inequalities; reason: as in Lemma 5.2: the quantities depend only on (y_i, u_i, v_i)
--   - encoding: polynomials in (t, H, V) → real functions given by the polynomial formulas; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.2, pp.72–73 (PDF pp.72–73)

import Mathlib
import Definitions.Def_KSPolySign_certZ
import Definitions.Def_KSPolySign_certQ
import Definitions.Def_KSPolySign_numZ
import Definitions.Def_KSPolySign_numP
import Definitions.Def_KSPolySign_numQ
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma A.2 (Polynomial certificate).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.2, pp.72–73 (PDF pp.72–73).

The polynomials `F_n, B_n, U_n, Q_n, Z_n, P_n` in `(t, H, V)` satisfy (147)
`min{F_n, B_n, U_n, Z_n, P_n} > 1/400` on `[0, 1]³`. At an active coordinate with `y ≥ 0` of a light
state, write `z = y`, `w = √(1 − z²)`, `δ`, `k` as in Definitions 3.19, 3.20 and `s_inv = 1/k`; if
`(t, H, V) ∈ [0, 1) × [0, 1]²` satisfies (148) `z = 2t/(1 + t²)`, `w = (1 − t²)/(1 + t²)`, `δ = (w/ι)H`,
`s_inv = (2η/ι)w(1 + z(1 − H)(2V − 1))`, then with `g = 1 + t²` (149):
`F = F_n/g²`, `B = B_n/g²`, `𝔲 = U_n/g⁵`, `𝔮 = Q_n/g⁶`, `𝔷 = Z_n/g⁶`.

**Formalization Note** The polynomials are the explicit ones defined in the proof (p.73), as real
polynomial functions (`numF`, …, `numP`). The light state's coordinate is the scalar triple
`(y, u, v)` as in Lemma 5.2. -/
theorem lemma_A_2 :
    (∀ t H V : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → H ∈ Set.Icc (0 : ℝ) 1 → V ∈ Set.Icc (0 : ℝ) 1 →
      1 / 400 < numF t H V ∧ 1 / 400 < numB t H V ∧ 1 / 400 < numU t H V ∧
        1 / 400 < numZ t H V ∧ 1 / 400 < numP t H V) ∧
    ∀ y u v : ℝ, 0 ≤ y → y < 1 → 0 < u → 0 < v →
      iota * beta y * u < 1 + y → iota * beta y * v < 1 - y →
      ∀ t H V : ℝ, 0 ≤ t → t < 1 → H ∈ Set.Icc (0 : ℝ) 1 → V ∈ Set.Icc (0 : ℝ) 1 →
        y = 2 * t / (1 + t ^ 2) → Real.sqrt (1 - y ^ 2) = (1 - t ^ 2) / (1 + t ^ 2) →
        deltaC y u v = Real.sqrt (1 - y ^ 2) / iota * H →
        1 / kC y u v = 2 * etaC / iota * Real.sqrt (1 - y ^ 2) * (1 + y * (1 - H) * (2 * V - 1)) →
        certF y u v = numF t H V / (1 + t ^ 2) ^ 2 ∧ certB y u v = numB t H V / (1 + t ^ 2) ^ 2 ∧
          certU y u v = numU t H V / (1 + t ^ 2) ^ 5 ∧ certQ y u v = numQ t H V / (1 + t ^ 2) ^ 6 ∧
          certZ y u v = numZ t H V / (1 + t ^ 2) ^ 6 := by sorry

end KSPolySign
