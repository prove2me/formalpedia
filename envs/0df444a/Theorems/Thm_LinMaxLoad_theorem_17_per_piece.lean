-- Prove2me | Theorems.Thm_LinMaxLoad_theorem_17_per_piece
-- name    : LinMaxLoad.theorem_17_per_piece
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:35:38.826364+00:00
-- url     : https://prove2.me/theorems/ef40219e-7a15-4edc-9c70-e0a9726351a6
-- title:
--   Proof of Theorem 17 — per-piece bound $\mathbb E_h[M(V+T,h)] = O(p/\varepsilon)$
-- statement:
--   Let $p$ be a prime, $0 < \varepsilon \le 1$, $S \subseteq \mathbb F_p^u$ a finite set, $\ell := \lceil \log_p |S| \rceil$, and $h : \mathbb F_p^u \to \mathbb F_p^\ell$ a uniformly random linear map. For every subspace $V \le \mathbb F_p^u$ and finite $T \subseteq \mathbb F_p^u$ with
--
--   $$
--   |V| \le |S| \quad \text{and} \quad |T| \le \big(|S|/|V|\big)^{1 - \varepsilon},
--   $$
--
--   we have
--
--   $$
--   \mathbb E_h\big[M(V + T, h)\big] \le c\, \frac{p}{\varepsilon}
--   $$
--
--   for an absolute constant $c$, independent of $p$, $u$, $\varepsilon$, $S$, $V$ and $T$.
--
--   By subadditivity of max load, summing this bound over the $C$ pieces $V_i + T_i$ of a cover gives Theorem 17.
--
--   Differences from the source:
--   - reading: $O(p/\varepsilon)$ → $c\,p/\varepsilon$ with one absolute real constant $c$ chosen before $p$ and all data; reason: the strongest reading of an absolute $O$; the bound carries $p$ and $\varepsilon$ explicitly
--   - encoding: $\mathbb F_p^u$, $\lceil\log_p|S|\rceil$, $(|S|/|V|)^{1-\varepsilon}$ → `Fin u → ZMod p`, `Nat.clog p S.card`, real power `Real.rpow`; reason: Lean convention; same values
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Theorem 17, per-piece bound, p.24

import Mathlib
import Definitions.Def_LinMaxLoad_expLoad
import Definitions.Def_LinMaxLoad_cosetSum

namespace LinMaxLoad

/-- **Proof of Theorem 17, per-piece bound** (p.24 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `0 < ε ≤ 1`, `S ⊆ F_p^u` finite, `ℓ := ⌈log_p |S|⌉`, `h : F_p^u → F_p^ℓ` a uniformly random
linear map. For every subspace `V` and finite `T` with `|V| ≤ |S|` and
`|T| ≤ (|S|/|V|)^{1−ε}`, `E_h[M(V + T, h)] = O(p/ε)`.

**Formalization Note** `O(p/ε)` is `c·p/ε` with one absolute constant `c` chosen before `p` and
all data. `F_p^u = Fin u → ZMod p`, `ℓ = Nat.clog p |S|`, sizes `|V| = Nat.card V`, and
`(|S|/|V|)^{1−ε}` is a real power. -/
theorem theorem_17_per_piece :
    ∃ c : ℝ, ∀ (p : ℕ) [Fact p.Prime] (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (S : Finset (Fin u → ZMod p)) (V : Submodule (ZMod p) (Fin u → ZMod p))
        (T : Finset (Fin u → ZMod p)),
        Nat.card V ≤ S.card →
        ((T.card : ℝ) ≤ ((S.card : ℝ) / Nat.card V) ^ (1 - ε)) →
        expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card) (cosetSum V T) ≤ c * p / ε := by sorry

end LinMaxLoad
