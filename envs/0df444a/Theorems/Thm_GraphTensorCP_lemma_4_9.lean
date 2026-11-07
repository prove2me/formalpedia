-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_4_9
-- name    : GraphTensorCP.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:10.579673+00:00
-- url     : https://prove2.me/theorems/c890cc73-a26c-4f9e-aa2e-72df70c17e16
-- title:
--   Lemma 4.9 — diagonal growth $F(a,\dots,a)\ge a^{2(n-1)/n}$
-- statement:
--   Let $n\ge3$. Suppose that $F:\mathbb N_{>0}^{\,n-1}\to\mathbb R_{>0}$ is symmetric, that $F(1,\dots,1)=1$, and that $F$ satisfies
--
--   1. (discrete concavity, as in Lemma 4.5) $2F(\dots,b,\dots)\ge F(\dots,b+1,\dots)+F(\dots,b-1,\dots)$ for every integer $b\ge2$, in every coordinate, the other arguments being arbitrary positive integers;
--   2. (shifted tripling, as in Lemma 4.8) $F(\dots,3h+S,\dots)\ge3F(\dots,h,\dots)$ for every positive integer $h$, in every coordinate, where $S$ is the sum of $a_i-1$ over the other arguments $a_i$.
--
--   Then for every positive integer $a$,
--
--   $$F(\underbrace{a,\dots,a}_{n-1})\ge a^{2(n-1)/n}.$$
--
--   This is a purely real-variable lemma; applied to the profile $P_\phi$ it bounds the average spectral edge weight $t_\phi$.
--
--   **Formalization Note** $F$ is a function on all of $\mathbb N^{n-1}$, and every hypothesis, including positivity, is imposed on positive tuples only. Concavity and tripling are assumed in every coordinate, as Lemmas 4.5 and 4.8 state them; given symmetry this is equivalent to assuming them in the last coordinate.
--
--   Differences from the source:
--   - encoding: $F:\mathbb N_{>0}^{n-1}\to\mathbb R_{>0}$ → $F:(\mathrm{Fin}(n-1)\to\mathbb N)\to\mathbb R$ with positivity and all hypotheses on positive tuples; reason: values off the positive tuples are never used; same instances
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 4.9, p.42

import Mathlib

namespace GraphTensorCP

/-- **Lemma 4.9** (diagonal growth), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.42:
"Let n ≥ 3 be an integer. Suppose that F : ℕ_{>0}^{n−1} → ℝ_{>0} is symmetric, that F(1, . . . , 1) = 1, and
that it satisfies the concavity and shifted tripling inequalities in Lemmas 4.5 and 4.8, with F in
place of P_ϕ. Then, for every positive integer a, F(a, . . . , a) ≥ a^{2(n−1)/n} (n − 1 coordinates)."

**Formalization Note.** `F` is a function on all of `ℕ^{n−1}` (`Fin (n−1) → ℕ`); every hypothesis
is imposed on positive tuples only, so only the values on `ℕ_{>0}^{n−1}` matter, and positivity of
those values is the hypothesis `hpos`. Symmetry is invariance under every permutation of the
arguments. Concavity and shifted tripling are assumed in every input coordinate, as Lemmas 4.5 and
4.8 state them (given symmetry this is equivalent to assuming them in the last coordinate).
In tripling, `S = Σ_{i ≠ j} (a i − 1)`. -/
theorem lemma_4_9 {n : ℕ} (hn3 : 3 ≤ n) (F : (Fin (n - 1) → ℕ) → ℝ)
    (hpos : ∀ a : Fin (n - 1) → ℕ, (∀ i, 0 < a i) → 0 < F a)
    (hsymm : ∀ (σ : Equiv.Perm (Fin (n - 1))) (a : Fin (n - 1) → ℕ), (∀ i, 0 < a i) →
      F (a ∘ σ) = F a)
    (hone : F (fun _ => 1) = 1)
    (hconc : ∀ (j : Fin (n - 1)) (a : Fin (n - 1) → ℕ), (∀ i, 0 < a i) → ∀ b : ℕ, 2 ≤ b →
      F (Function.update a j (b + 1)) + F (Function.update a j (b - 1)) ≤
        2 * F (Function.update a j b))
    (htrip : ∀ (j : Fin (n - 1)) (a : Fin (n - 1) → ℕ), (∀ i, 0 < a i) → ∀ h : ℕ, 0 < h →
      3 * F (Function.update a j h) ≤
        F (Function.update a j (3 * h + ∑ i ∈ Finset.univ.erase j, (a i - 1)))) :
    ∀ a : ℕ, 0 < a → (a : ℝ) ^ ((2 * ((n : ℝ) - 1)) / n) ≤ F (fun _ => a) := by sorry

end GraphTensorCP
