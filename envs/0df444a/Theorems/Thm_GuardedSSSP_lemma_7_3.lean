-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_7_3
-- name    : GuardedSSSP.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:12.293875+00:00
-- url     : https://prove2.me/theorems/4b375acd-a838-4746-bf9d-56d93ce5aca0
-- title:
--   Lemma 7.3 — uniform stability of $f_d$ and $\Phi$, and the quota bounds (27)
-- statement:
--   1. For every multiplier $\kappa>0$ there is $C\ge1$ such that for every $d$ and every $x\ge0$,
--   $$C^{-1}f_d(x)\le f_d(\kappa x)\le Cf_d(x),\qquad C^{-1}\Phi(x)\le\Phi(\kappa x)\le C\Phi(x)$$
--   (written as $f_d(x)\le Cf_d(\kappa x)$ and $f_d(\kappa x)\le Cf_d(x)$, and likewise for $\Phi$).
--   2. For every $c\ge2$ there is $t_0$ such that for every real $t\ge t_0$ and every $d$, with $q=\lfloor t/(cf_d(t))\rfloor$,
--   $$\tfrac12L_i(t)\le L_i(q)\le L_i(t)\ (i\ge1),\qquad \tfrac12f_d(t)\le f_d(q)\le f_d(t).$$
--   3. For every $c\ge2$ and every $j\in\mathbb N$ there are $\theta>0$ and $t_0$ such that for every $t\ge t_0$, every $d$ and every real $q'$ with $2^{-j}q\le q'\le2^jq$,
--   $$\theta L_i(t)\le L_i(q')\le L_i(t)\ (i\ge1),\qquad \theta f_d(t)\le f_d(q')\le f_d(t).$$
--
--   Rounding a width or reserving quota slack therefore costs a constant factor independent of the generation.
--
--   Differences from the source:
--   - reading: the fixed-multiplier stability constants of all f_d and of Φ can be chosen independently of d → ∀ κ > 0 ∃ C ≥ 1 ∀ d ∀ x ≥ 0, two-sided factor-C bounds for f_d and Φ; reason: the meaning of stability under a fixed multiplier, uniform in d
--   - generalization: for one fixed c ≥ 2 → for every c ≥ 2, with t₀ chosen after c; reason: specializes to the paper's fixed c
--   - generalization: width t (an integer in the algorithm) → every real t ≥ t₀; reason: contains the integer widths
--   - reading: the lower factor 1/2 can be replaced by another fixed positive constant when bounded dyadic rounding is included → ∀ c ≥ 2 ∀ j ∃ θ > 0, t₀ such that every q′ within a factor 2^j of q satisfies the bounds with θ; reason: rounding in either direction by a bounded dyadic factor, the stronger of the possible readings
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 7.3, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

/-- **Lemma 7.3** (Uniform stability), p.15 (PDF p.16).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Fix absolute positive multipliers. The fixed-multiplier
stability constants of all f_d and of Φ can be chosen independently of d. Moreover, for one fixed c ≥ 2,
if q = ⌊t/(c f_d(t))⌋, then, for every sufficiently large absolute t and every d,
½L_i(t) ≤ L_i(q) ≤ L_i(t) (i ≥ 1), ½f_d(t) ≤ f_d(q) ≤ f_d(t). (27) The lower factor 1/2 can be replaced
by another fixed positive constant when bounded dyadic rounding is included."

Three clauses:
1. (stability) for every multiplier `κ > 0` there is `C ≥ 1` such that for every `d` and every
   `x ≥ 0`, `f_d(κx)` and `f_d(x)` agree within the factor `C`, and so do `Φ(κx)` and `Φ(x)`;
2. (27) for every `c ≥ 2`: there is `t₀` such that for all `t ≥ t₀`, all `d` and all `i ≥ 1`, with
   `q = ⌊t/(c f_d(t))⌋`, the bounds (27) hold;
3. (dyadic rounding) for every `c ≥ 2` and every `j`, there are `θ > 0` and `t₀` such that for all
   `t ≥ t₀`, all `d` and every real `q'` with `2^{−j}q ≤ q' ≤ 2^{j}q`, `θL_i(t) ≤ L_i(q') ≤ L_i(t)`
   for `i ≥ 1` and `θf_d(t) ≤ f_d(q') ≤ f_d(t)`.

**Formalization Note.** The threshold `t₀` is chosen after `c` (and `j`) and before `t`, `d` and `i`:
uniform in the generation. "For one fixed c ≥ 2" is stated for every `c ≥ 2`. The width `t` is real;
the quota is `⌊·⌋₊` cast to `ℝ`. -/
theorem lemma_7_3 :
    (∀ κ : ℝ, 0 < κ → ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) (x : ℝ), 0 ≤ x →
      f d x ≤ C * f d (κ * x) ∧ f d (κ * x) ≤ C * f d x ∧
      Phi x ≤ C * Phi (κ * x) ∧ Phi (κ * x) ≤ C * Phi x) ∧
    (∀ c : ℝ, 2 ≤ c → ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ d : ℕ,
      let q : ℝ := (⌊t / (c * f d t)⌋₊ : ℝ)
      (∀ i : ℕ, 1 ≤ i → L i t / 2 ≤ L i q ∧ L i q ≤ L i t) ∧
      f d t / 2 ≤ f d q ∧ f d q ≤ f d t) ∧
    (∀ c : ℝ, 2 ≤ c → ∀ j : ℕ, ∃ θ t₀ : ℝ, 0 < θ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ (d : ℕ) (q' : ℝ),
      let q : ℝ := (⌊t / (c * f d t)⌋₊ : ℝ)
      q / 2 ^ j ≤ q' → q' ≤ 2 ^ j * q →
      (∀ i : ℕ, 1 ≤ i → θ * L i t ≤ L i q' ∧ L i q' ≤ L i t) ∧
      θ * f d t ≤ f d q' ∧ f d q' ≤ f d t) := by sorry

end GuardedSSSP
