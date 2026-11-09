-- Prove2me | Theorems.Thm_LinMaxLoad_theorem_17
-- name    : LinMaxLoad.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:37.122708+00:00
-- url     : https://prove2.me/theorems/f099110b-6445-495d-890a-5702d93b25db
-- title:
--   Theorem 17 — covers by $C$ coset families $V_i+T_i$ with $|T_i|\le(|S|/|V_i|)^{1-\varepsilon}$ give $m(S) = O(pC/\varepsilon)$
-- statement:
--   Let $p$ be a prime, $0 < \varepsilon \le 1$, and $S \subseteq \mathbb F_p^u$ a finite set. Suppose that for some subspaces $V_1, \dots, V_C \le \mathbb F_p^u$ of size at most $|S|$ and subsets $T_1, \dots, T_C \subseteq \mathbb F_p^u$ with
--
--   $$
--   |T_i| \le \left( \frac{|S|}{|V_i|} \right)^{1 - \varepsilon},
--   $$
--
--   we have
--
--   $$
--   S \subseteq \bigcup_{i=1}^{C} (V_i + T_i).
--   $$
--
--   Then the expected linear max load of $S$ satisfies
--
--   $$
--   m(S) \le c\, \frac{p\, C}{\varepsilon}
--   $$
--
--   for an absolute constant $c$, independent of $p$, $u$, $C$, $\varepsilon$, $S$ and the cover. Here $m(S) = \mathbb E_h[M(S,h)]$ for a uniformly random linear map $h : \mathbb F_p^u \to \mathbb F_p^{\ell}$, $\ell = \lceil \log_p |S| \rceil$.
--
--   In words: if $S$ is covered by cosets of a bounded number of subspaces, where smaller subspaces may be used with more cosets, then linear hashing of $S$ has small expected max load. This is the paper's first main result (Theorem 3 in the introduction, with $\gamma$ in place of $\varepsilon$).
--
--   Differences from the source:
--   - reading: $O(pC/\varepsilon)$ → $c\,p\,C/\varepsilon$ with one absolute real constant $c$ chosen before $p$, $u$, $C$, $\varepsilon$ and all sets; reason: the strongest reading of an absolute $O$; the bound carries $p$, $C$ and $\varepsilon$ explicitly
--   - encoding: indices $i = 1, \dots, C$; $\mathbb F_p^u$; $|V_i|$; $(|S|/|V_i|)^{1-\varepsilon}$ → `Fin C` (0-based); `Fin u → ZMod p`; `Nat.card (V i)`; real power `Real.rpow`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 17, p.23, proof p.24 (introduction form Theorem 3, p.5)

import Mathlib
import Definitions.Def_LinMaxLoad_linMaxLoad

namespace LinMaxLoad

open Pointwise in
/-- **Theorem 17** (p.23, proof p.24; introduction form Theorem 3, p.5, with `γ` for `ε`) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d).
Let `0 < ε ≤ 1` and `S ⊆ F_p^u` such that for some subspaces `V₁, …, V_C ≤ F_p^u` of size at
most `|S|` and subsets `T₁, …, T_C ⊆ F_p^u` with `|T_i| ≤ (|S|/|V_i|)^{1−ε}`, we have
`S ⊆ ⋃_{i=1}^C (V_i + T_i)`. Then `m(S) ≤ O(pC/ε)`.

**Formalization Note** `O(pC/ε)` is `c·p·C/ε` with one absolute real constant `c` chosen before
`p`, `u`, `C`, `ε` and all sets. `F_p^u = Fin u → ZMod p`; `m(S)` is `linMaxLoad` (with
`ℓ = ⌈log_p |S|⌉`, `h` uniform over all linear maps); indices `Fin C` are 0-based; `V_i + T_i` is
the pointwise sum of sets; `|V_i| = Nat.card (V i)`; `(|S|/|V_i|)^{1−ε}` is a real power. `C = 0`
is allowed (then `S = ∅`). -/
theorem theorem_17 :
    ∃ c : ℝ, ∀ (p : ℕ) [Fact p.Prime] (u C : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (S : Finset (Fin u → ZMod p)) (V : Fin C → Submodule (ZMod p) (Fin u → ZMod p))
        (T : Fin C → Finset (Fin u → ZMod p)),
        (∀ i, Nat.card (V i) ≤ S.card) →
        (∀ i, ((T i).card : ℝ) ≤ ((S.card : ℝ) / Nat.card (V i)) ^ (1 - ε)) →
        ((S : Set (Fin u → ZMod p)) ⊆ ⋃ i, ((V i : Set (Fin u → ZMod p)) + ((T i : Finset _) : Set (Fin u → ZMod p)))) →
        linMaxLoad p u S ≤ c * p * C / ε := by sorry

end LinMaxLoad
