-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_15
-- name    : LinMaxLoad.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:43.116358+00:00
-- url     : https://prove2.me/theorems/d3c9535b-cb5b-403c-a0ef-a2259aa9976b
-- title:
--   Theorem 15 — $\Pr[M(S,h) \le k] \ge \delta$ gives $E(S) \ge \frac{\delta (m/n)^k}{4k p^{4k^2}} m^3$
-- statement:
--   Let $p$ be a prime and let $u \ge \ell \ge 1$ and $m \le n := p^\ell$ be integers. Let $S \subseteq \mathbb F_p^u$ be a set of size $m$, and let $h : \mathbb F_p^u \to \mathbb F_p^\ell$ be a uniformly random linear map. If
--
--   $$
--   \Pr_h\bigl[M(S,h) \le k\bigr] \ge \delta \qquad\text{for some } k \text{ with } 2k p^k \le m,
--   $$
--
--   then the additive energy of $S$ satisfies
--
--   $$
--   E(S) \ge \frac{\delta\, (m/n)^k}{4k\, p^{4k^2}} \cdot m^3 .
--   $$
--
--   In particular, when $m = n$, $E(S) = \Omega_{\delta,p,k}(n^3)$: sets whose linear max load is bounded with constant probability have cubic additive energy.
--
--   Differences from the source:
--   - encoding: $k$ a (positive) integer; $\delta$ a probability bound → $k \in \mathbb N$ and $\delta \in \mathbb R$ unrestricted; reason: at $k = 0$ Lean's division by $4k = 0$ makes the bound $0$, and for $\delta \le 0$ the bound is $\le 0$; both cases are trivially true, so no instance of the source changes
--   - encoding: $\mathbb F_p^u$; $h$ into $\mathbb F_p^\ell$ with the theorem's $\ell$; $\Pr$; $E(S)$ → `Fin u → ZMod p`; published `probLin` with $r = \ell$; `addEnergy`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 15, p.16

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin
import Definitions.Def_LinMaxLoad_Supplement_addEnergy

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 15** (p.16) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `u ≥ ℓ ≥ 1`, `m ≤ n := p^ℓ` be integers. Let `S ⊆ F_p^u` be of size `m`, `h : F_p^u → F_p^ℓ` be
a uniformly random linear map. If `Pr[M(S, h) ≤ k] ≥ δ` for some `2kp^k ≤ m`, then
`E(S) ≥ δ(m/n)^k / (4k p^{4k²}) · m³`.

**Formalization Note** `h` maps into `F_p^ℓ` with the theorem's own `ℓ` (not `⌈log_p m⌉`);
`Pr` is the published `probLin` with `r = ℓ`, `M` is `maxLoad`, `E(S)` is `addEnergy`. The
"in particular" sentence (the case `m = n`) is a consequence and is not stated separately.
`k` ranges over all naturals: at `k = 0` Lean's division by `4k = 0` makes the bound `0`, so
that case is trivially true. `δ` is any real (for `δ ≤ 0` the bound is trivial). -/
theorem theorem_15 (p : ℕ) [Fact p.Prime] (u ℓ m k : ℕ) (S : Finset (Fin u → ZMod p)) (δ : ℝ)
    (hℓ : 1 ≤ ℓ) (hu : ℓ ≤ u) (hm : m ≤ p ^ ℓ) (hS : S.card = m) (hk : 2 * k * p ^ k ≤ m)
    (hδ : δ ≤ probLin (ZMod p) (Fin u → ZMod p) ℓ
      fun h => maxLoad (h : (Fin u → ZMod p) → Fin ℓ → ZMod p) S ≤ k) :
    δ * ((m : ℝ) / (p : ℝ) ^ ℓ) ^ k / (4 * k * (p : ℝ) ^ (4 * k ^ 2)) * (m : ℝ) ^ 3
      ≤ (addEnergy S : ℝ) := by sorry

end LinMaxLoad.Supplement
