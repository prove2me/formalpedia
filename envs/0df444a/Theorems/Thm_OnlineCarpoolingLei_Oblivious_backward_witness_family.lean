-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_backward_witness_family
-- name    : OnlineCarpoolingLei.Oblivious.backward_witness_family
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:38.486203+00:00
-- url     : https://prove2.me/theorems/b726e716-7aee-4b1d-b50c-74ae9a73b059
-- title:
--   Lemma 4.2 — an input-determined witness family $W_D$ with $|W_D|\le2T\cdot3^\ell$
-- statement:
--   Fix $T$ and an integer $D\ge300$, and let $K=\lfloor D/40\rfloor$, $\ell=\lceil D^2/80\rceil$. For edges $e_1,\dots,e_T$ on $[n]$ there is a family $W_D$ of pairs $(t,S)$ with $0\le t\le T$ and $S\subseteq[n]$, determined only by $e_1,\dots,e_T$ and $D$, such that
--   $$|W_D|\le2T\cdot3^{\ell},\qquad 1\le|S|\le K\quad\text{for every }(t,S)\in W_D .$$
--   For every trajectory with receiving gap at most $29$ and $M_T\ge D$, some $(t_0,S)\in W_D$ satisfies
--   $$|d_{t_0}(S)|\ge\frac{D^2}{80}.$$
--   The elements of $W_D$ are called witnesses.
--
--   Because $W_D$ does not depend on the trajectory, a union bound over its elements turns a tail bound for each fixed $d_t(S)$ into a bound on $\mathbb P(M_T\ge D)$; this is how Theorem 1.2 is derived.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$, edges $e_1,\dots,e_T$ → `Fin n`, `E : ℕ → Edge n` (first $T$ entries); reason: relabelling
--   - encoding: "$W_D$ determined only by $e_1,\dots,e_T$ and $D$" → a function `W` of the input, chosen after $T$ and $D$ and before any trajectory, with `W E = W E'` whenever `E` and `E'` agree on their first $T$ entries; reason: this is what "determined only by" means
--   - encoding: integer $D\ge300$ → `D : ℕ` with `300 ≤ D`; reason: same set of values
--   - encoding: a signed-edge trajectory (d_t) for 0 ≤ t ≤ T → traj E ε restricted to 0,…,T, with ε : ℕ → ℤ and IsSignSeq ε; reason: every finite valid trajectory extends by arbitrary ±1 signs; neither conclusion depends on signs after T
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 4.2, p.8 (PDF p.8); Section 4 preamble, p.6; (4.1) p.6

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Threshold

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 4.2 (p.8). Fix `T` and an integer `D ≥ 300`. There is a family `W_D` of pairs `(t, S)`
with `0 ≤ t ≤ T` and `S ⊆ [n]`, determined only by `e₁, …, e_T` and `D`, with
`|W_D| ≤ 2T · 3^ℓ` and `1 ≤ |S| ≤ K` for every `(t, S) ∈ W_D`, such that every trajectory with
receiving gap at most `29` and `M_T ≥ D` has some `(t₀, S) ∈ W_D` with `|d_{t₀}(S)| ≥ D²/80`.
The family is a function of the input that depends only on its first `T` edges, chosen before
any trajectory. -/
theorem backward_witness_family {n : ℕ} (T D : ℕ) (hD : 300 ≤ D) :
    ∃ W : (ℕ → Edge n) → Finset (ℕ × Finset (Fin n)),
      (∀ E E' : ℕ → Edge n, (∀ t < T, E t = E' t) → W E = W E') ∧
      ∀ E : ℕ → Edge n,
        (W E).card ≤ 2 * T * 3 ^ ellc D ∧
        (∀ w ∈ W E, w.1 ≤ T ∧ 1 ≤ w.2.card ∧ w.2.card ≤ Kc D) ∧
        ∀ ε : ℕ → ℤ, IsSignSeq ε → GapAtMost E ε T 29 → D ≤ maxDisc (traj E ε) T →
          ∃ w ∈ W E, ((D : ℝ) ^ 2) / 80 ≤ |(setSum (traj E ε w.1) w.2 : ℝ)| := by sorry

end OnlineCarpoolingLei.Oblivious
