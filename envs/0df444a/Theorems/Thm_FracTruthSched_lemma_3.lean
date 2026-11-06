-- Prove2me | Theorems.Thm_FracTruthSched_lemma_3
-- name    : FracTruthSched.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:29:03.400588+00:00
-- url     : https://prove2.me/theorems/bb0374b0-753d-4245-a53d-3089372e5e63
-- title:
--   Lemma 3 (Fixed-star retention) — $N_u\ge(1-1/\ell)^{k-1}\sum_j q_j$
-- statement:
--   Let $D$ be a finite set of tasks partitioned into $k$ classes $D_1,\dots,D_k$, each of size $\ell$, and choose $e_j\in D_j$; set $S=\{e_1,\dots,e_k\}$. Let $V$ be a function of the values $a\in\mathbb R^D_{\ge0}$ and $x_e(a)\ge0$ fractions satisfying the incentive inequalities
--   $$x(b)\cdot(b-a)\le V(b)-V(a)\le x(a)\cdot(b-a)\qquad(a,b\in\mathbb R^D_{\ge0}),\tag{4}$$
--   as do a machine's disutility and allocation in a truthful fractional mechanism when its values on $D$ vary and all other values are fixed. Let $q_j=x_{e_j}(\mathbf 1_{e_j})$ and, for $0<u<1$, $N_u=\sum_{j=1}^k x_{e_j}(u\mathbf 1_S)$.
--
--   Suppose that $V$ is additive and symmetric within each class $D_j$, for every fixed choice of values on the other classes. Then, for every $0<u<1$,
--   $$N_u\ \ge\ \Big(1-\frac1\ell\Big)^{k-1}\sum_{j=1}^k q_j.$$
--
--   The factor $(1-1/\ell)^{k-1}$ is the price of interactions between classes, and it tends to $1$ as $\ell\to\infty$.
--
--   Differences from the source:
--   - generalization: V and x_e the disutility and allocation of a fixed machine of a truthful fractional mechanism, its values on D varying and all other values fixed → any functions V : (D → ℝ) → ℝ and x : (D → ℝ) → D → ℝ with x ≥ 0 and the incentive inequalities (4) at all nonnegative a, b; reason: the proof uses only (4), x ≥ 0 and the additivity/symmetry hypothesis; a truthful mechanism's disutility and allocation satisfy these (§2.3), so the statement specializes to the source's
--   - encoding: a partition of D into k classes D_1, …, D_k of size ℓ → a finite type τ with a class map cl : τ → Fin k whose fibres have ℓ elements; e : Fin k → τ with cl (e j) = j; reason: same data
--   - encoding: 1_{e_j} and u 1_S, zero elsewhere in D → Pi.single (e j) 1 and the function equal to u on the image of e and 0 elsewhere; reason: same vectors
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 3, p.14 (setup p.13; (4), p.5)

import Mathlib
import Definitions.Def_FracTruthSched_IsAdditiveOn
import Definitions.Def_FracTruthSched_IsSymmetricOn

set_option autoImplicit false

namespace FracTruthSched

/-- **Lemma 3 (Fixed-star retention)** (Anastasiadis et al., arXiv:2611.06642v1, Lemma 3, p.14, setup
p.13). Fix a machine of a truthful fractional mechanism and its values on a set `D` of tasks, all
other values fixed; `V(a)` is its disutility and `x_e(a)` its fraction of task `e` when its values on
`D` are `a`. Partition `D` into `k` classes `D_1, …, D_k` of size `ℓ`, choose `e_j ∈ D_j`, and set
`S = {e_1, …, e_k}`, `q_j = x_{e_j}(1_{e_j})`, `N_u = Σ_j x_{e_j}(u 1_S)`. If `V` is additive and
symmetric within each class `D_j`, for every fixed choice of values on the other classes, then for
every `0 < u < 1`, `N_u ≥ (1 − 1/ℓ)^{k−1} Σ_{j=1}^k q_j`.

**Formalization Note.** Stated abstractly: `D` is a finite type `τ`, the classes are the fibres of
`cl : τ → Fin k`, each of size `ℓ`, and `V`, `x` are any functions with `x ≥ 0` and the incentive
inequalities (4) `x(b)·(b − a) ≤ V(b) − V(a) ≤ x(a)·(b − a)` at all nonnegative `a, b`. A machine's
disutility and allocation in a truthful mechanism satisfy these hypotheses (§2.3, p.5), so this
specializes to the lemma. -/
theorem lemma_3 {τ : Type*} [Fintype τ] [DecidableEq τ] {k ℓ : ℕ} (cl : τ → Fin k)
    (hcard : ∀ j, (Finset.univ.filter (fun d => cl d = j)).card = ℓ)
    (V : (τ → ℝ) → ℝ) (x : (τ → ℝ) → τ → ℝ)
    (hx : ∀ a, (∀ d, 0 ≤ a d) → ∀ d, 0 ≤ x a d)
    (hinc : ∀ a b, (∀ d, 0 ≤ a d) → (∀ d, 0 ≤ b d) →
      ∑ d, x b d * (b d - a d) ≤ V b - V a ∧ V b - V a ≤ ∑ d, x a d * (b d - a d))
    (hadd : ∀ j, IsAdditiveOn V (Finset.univ.filter (fun d => cl d = j)))
    (hsym : ∀ j, IsSymmetricOn V (Finset.univ.filter (fun d => cl d = j)))
    (e : Fin k → τ) (he : ∀ j, cl (e j) = j) (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    (1 - 1 / (ℓ : ℝ)) ^ (k - 1) * ∑ j, x (Pi.single (e j) 1) (e j) ≤
      ∑ j, x (fun d => if d ∈ Finset.univ.image e then u else 0) (e j) := by sorry

end FracTruthSched
