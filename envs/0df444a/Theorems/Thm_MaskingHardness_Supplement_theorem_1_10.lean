-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_10
-- name    : MaskingHardness.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:32:59.037839+00:00
-- url     : https://prove2.me/theorems/03685ef4-4f2c-458f-b433-46ccd2f38038
-- title:
--   Theorem 1.10 — hinge, $\ell_1$ and $\ell_p$ hardcore lemmas
-- statement:
--   Fix a finite set $\mathcal X$, a distribution over pairs $(x,y)\in\mathcal X\times\{\pm1\}$, a finite class $\mathcal C\subseteq\{\mathcal X\to\mathbb R\}$ and $\varepsilon>0$. For $\lambda\in\mathbb R^{\mathcal C}$ write $c_\lambda=\sum_{c\in\mathcal C}\lambda_c c$ and $\|\lambda\|_1=\sum_c|\lambda_c|$, and abbreviate $\mu=\mu(x,y)$. Then all three of the following hold, with both the minimum and the maximum attained:
--
--   $$
--   \min_{\lambda}\ \mathbb E\big[(1-c_\lambda(x)y)_+\big]+\varepsilon\|\lambda\|_1=\max_{\mu:\mathcal X\times\mathcal Y\to[0,1]}\mathbb E[\mu]\quad\text{s.t. }\forall c\in\mathcal C,\ \big|\mathbb E[\mu\,c(x)\,y]\big|\le\varepsilon, \tag{3}
--   $$
--
--   $$
--   \min_{\lambda}\ \mathbb E\big[|y-c_\lambda(x)|\big]+\varepsilon\|\lambda\|_1=\max_{\mu:\mathcal X\times\mathcal Y\to[-1,1]}\mathbb E[\mu]\quad\text{s.t. }\forall c\in\mathcal C,\ \big|\mathbb E[\mu\,c(x)\,y]\big|\le\varepsilon, \tag{4}
--   $$
--
--   $$
--   \min_{\lambda}\ \mathbb E\Big[\tfrac1p|y-c_\lambda(x)|^p\Big]+\varepsilon\|\lambda\|_1=\max_{\mu:\mathcal X\times\mathcal Y\to\mathbb R}\mathbb E\Big[\mu-\tfrac1q|\mu|^q\Big]\quad\text{s.t. }\forall c\in\mathcal C,\ \big|\mathbb E[\mu\,c(x)\,y]\big|\le\varepsilon, \tag{5}
--   $$
--
--   where in (5) $p,q>1$ are any reals with $1/p+1/q=1$.
--
--   Equation (3) is the binary hardcore lemma in exact form: the least regularized hinge loss equals the largest density of a measure on which the labels look unbiased to $\mathcal C$. Equations (4) and (5) are the analogues for $\ell_1$ and $\ell_p$ losses, with signed (and, for (5), unbounded but penalized) measures.
--
--   **Formalization Note** Each equality is "there is a real $v$ that is the least value of the left objective and the greatest feasible value of the right objective".
--
--   Differences from the source:
--   - encoding: labels y ∈ {±1} → Bool, with real value signVal y = ±1 in every formula; reason: a two-element label type; only the values ±1 are used
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝ with c_λ(x) = ∑ᵢ λᵢ cᵢ(x); reason: an indexed family with ι = C recovers the set; repeated members change neither side
--   - encoding: min_λ … = max … (both sides attained) → ∃ v : ℝ, IsLeast of the range of the left objective and IsGreatest of the set of feasible right values; reason: "min" and "max" assert attainment; one common value v says the two optima are equal
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.10, Eqs. (3)–(5), p.7 (PDF p.9); restated p.23 (PDF p.25), proof p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_Supplement_signVal

namespace MaskingHardness.Supplement

/-- **Theorem 1.10** (Hinge, ℓ1, and ℓp Hardcore Lemmas) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.10, printed p.7 = PDF
p.9; restated printed p.23 = PDF p.25, proof p.24 = PDF p.26).

Fix a finite set `X`, a distribution over pairs `(x, y) ∈ X × {±1}`, a finite `C ⊆ {X → ℝ}` and
`ε > 0`. With `c_λ(x) = ∑_{c ∈ C} λ_c c(x)`:
(3) `min_λ E[(1 − c_λ(x)y)₊] + ε‖λ‖₁ = max_{µ : X×Y→[0,1]} E[µ]` s.t. `∀ c ∈ C, |E[µ c(x) y]| ≤ ε`;
(4) `min_λ E[|y − c_λ(x)|] + ε‖λ‖₁ = max_{µ : X×Y→[−1,+1]} E[µ]` s.t. the same constraint;
(5) `min_λ E[(1/p)|y − c_λ(x)|^p] + ε‖λ‖₁ = max_{µ : X×Y→ℝ} E[µ − (1/q)|µ|^q]` s.t. the same
constraint, for all reals `p, q > 1` with `1/p + 1/q = 1`.

**Formalization Note** "min = max" is: there is a real `v` that is the least value of the left
objective over `λ ∈ ℝ^C` (`IsLeast` of its range) and the greatest value of the right objective
over feasible `µ` (`IsGreatest`). Labels are `Bool` with real value `signVal y = ±1`; `D` is
given by weights (`IsDist`); `C` is a finite indexed family `c : ι → X → ℝ`; `‖λ‖₁ = ∑ᵢ |λᵢ|`;
`|·|^p` is `Real.rpow` of a nonnegative base. -/
theorem theorem_1_10 {X ι : Type*} [Fintype X] [Fintype ι]
    (D : X → Bool → ℝ) (hD : IsDist D) (c : ι → X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∃ v : ℝ,
      IsLeast (Set.range fun lam : ι → ℝ =>
          ∑ x, ∑ y, D x y * max 0 (1 - (∑ i, lam i * c i x) * signVal y) +
            ε * ∑ i, |lam i|) v ∧
      IsGreatest {u : ℝ | ∃ μ : X → Bool → ℝ, (∀ x y, μ x y ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, |∑ x, ∑ y, D x y * (μ x y * c i x * signVal y)| ≤ ε) ∧
          u = ∑ x, ∑ y, D x y * μ x y} v) ∧
    (∃ v : ℝ,
      IsLeast (Set.range fun lam : ι → ℝ =>
          ∑ x, ∑ y, D x y * |signVal y - ∑ i, lam i * c i x| + ε * ∑ i, |lam i|) v ∧
      IsGreatest {u : ℝ | ∃ μ : X → Bool → ℝ, (∀ x y, μ x y ∈ Set.Icc (-1 : ℝ) 1) ∧
          (∀ i, |∑ x, ∑ y, D x y * (μ x y * c i x * signVal y)| ≤ ε) ∧
          u = ∑ x, ∑ y, D x y * μ x y} v) ∧
    (∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q = 1 →
      ∃ v : ℝ,
        IsLeast (Set.range fun lam : ι → ℝ =>
            ∑ x, ∑ y, D x y * ((1 / p) * |signVal y - ∑ i, lam i * c i x| ^ p) +
              ε * ∑ i, |lam i|) v ∧
        IsGreatest {u : ℝ | ∃ μ : X → Bool → ℝ,
            (∀ i, |∑ x, ∑ y, D x y * (μ x y * c i x * signVal y)| ≤ ε) ∧
            u = ∑ x, ∑ y, D x y * (μ x y - (1 / q) * |μ x y| ^ q)} v) := by sorry

end MaskingHardness.Supplement
