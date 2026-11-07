-- Prove2me | Theorems.Thm_MonDepMW_theorem_5_7
-- name    : MonDepMW.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:03.08326+00:00
-- url     : https://prove2.me/theorems/8e8a9d20-6254-4426-8cbc-ee318efbf1c5
-- title:
--   Theorem 5.7 — Haussler's Packing Lemma
-- statement:
--   Let $\mathcal F$ be a set system over a finite set $U$ with $|\mathcal F|\geqslant2$, and let $c,\rho\geqslant1$ be reals and $k,d$ positive integers such that:
--
--   1. $|\{F\cap X:F\in\mathcal F\}|\leqslant c\cdot|X|^\rho$ for all $\emptyset\neq X\subseteq U$;
--   2. $\mathcal F$ has VC dimension at most $d$;
--   3. $|F\triangle F'|\geqslant k$ for all distinct $F,F'\in\mathcal F$.
--
--   Then
--   $$|\mathcal F|\leqslant2c\left(\frac{4d\,|U|}{k}\right)^{\rho}\leqslant\mathcal O_{d,\rho,k}\left(c\,|U|^\rho\right).$$
--
--   This classical bound is applied with $\rho=1$ to neighborhood set systems in Lemma 5.9.
--
--   **Formalization Note** The hidden factor of the last bound is a real $K$ chosen from $\rho,k,d$ before $c,U,\mathcal F$.
--
--   Differences from the source:
--   - encoding: 𝒪_{d,ρ,k}(c·|U|^ρ) → K·(c·|U|^ρ) with K chosen from ρ, k, d before c, U, ℱ; reason: the decoration names what the hidden factor may depend on (p.11)
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 5.7, p.20

import Mathlib

set_option autoImplicit false

namespace MonDepMW

universe u

/-- **Theorem 5.7 (Haussler's Packing Lemma).** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.20: "Let ℱ be a set system over a finite set U with |ℱ| ⩾ 2 such that
the following properties hold for some reals c, ρ ⩾ 1 and numbers k, d ∈ N: |{F ∩ X : F ∈ ℱ}| ⩽ c · |X|^ρ for all ∅ ≠ X ⊆ U,
ℱ has VC dimension at most d, and |F △ F′| ⩾ k for all distinct F, F′ ∈ ℱ. Then |ℱ| ⩽ 2c · (4d · |U|/k)^ρ ⩽ 𝒪_{d,ρ,k}(c · |U|^ρ).
(5.1)"

**Formalization Note.** The hidden factor of (5.1) is `K`, chosen from `ρ, k, d` before `c`, `U`, `ℱ`. The VC dimension is
Mathlib's `Finset.vcDim`, "the maximum cardinality of a set X ⊆ U that is shattered" (p.12). -/
theorem theorem_5_7 (ρ : ℝ) (hρ : 1 ≤ ρ) (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ K : ℝ, ∀ (U : Type u) [Fintype U] [DecidableEq U] (ℱ : Finset (Finset U)) (c : ℝ), 1 ≤ c → 2 ≤ ℱ.card →
      (∀ X : Finset U, X.Nonempty → ((ℱ.image fun F => F ∩ X).card : ℝ) ≤ c * (X.card : ℝ) ^ ρ) →
      ℱ.vcDim ≤ d →
      (∀ F ∈ ℱ, ∀ F' ∈ ℱ, F ≠ F' → k ≤ (symmDiff F F').card) →
      (ℱ.card : ℝ) ≤ 2 * c * (4 * (d : ℝ) * (Fintype.card U : ℝ) / (k : ℝ)) ^ ρ ∧
      2 * c * (4 * (d : ℝ) * (Fintype.card U : ℝ) / (k : ℝ)) ^ ρ ≤ K * (c * (Fintype.card U : ℝ) ^ ρ) := by sorry

end MonDepMW
