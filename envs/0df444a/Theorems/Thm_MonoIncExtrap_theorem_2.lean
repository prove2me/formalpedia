-- Prove2me | Theorems.Thm_MonoIncExtrap_theorem_2
-- name    : MonoIncExtrap.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:36.148282+00:00
-- url     : https://prove2.me/theorems/f45be7dc-3831-48f8-8d21-c0310900f997
-- title:
--   Theorem 2, p.6 — Algorithm 1 finds an $\epsilon$-residual solution within $T$ iterations and $N$ evaluations
-- statement:
--   Assume the standing assumptions of §2: $\gamma_0>0$, $\delta\in(0,1)$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\epsilon>0$, $x^0\in\mathrm{dom}\,B$, Assumption 1 with $\mu>0$, and let $x^*$ be the solution of (1). Let $L_{\mathcal S},L_{\widehat{\mathcal S}}$ be as in Lemma 1. Then Algorithm 1 terminates and outputs an $\epsilon$-residual solution of (1) in at most $T$ iterations, and the number of evaluations of $F$ and of the resolvent of $B$ is at most $N$, where
--   $$
--   T=3+\Bigl\lceil2\log\Bigl(\frac{r_0(8+12\gamma_0L_{\mathcal S})}{3\epsilon\sqrt{1-2\nu^2}\min\{L_{\widehat{\mathcal S}}^{-1}\delta\xi,\gamma_0\}}\Bigr)\Big/\log\Bigl(1+\frac{2\mu}{1-\eta}\min\{L_{\widehat{\mathcal S}}^{-1}\delta\xi,\gamma_0\}\Bigr)\Bigr\rceil_+,
--   $$
--   $$
--   N=2T+\Bigl\lceil\log\Bigl(\frac{\xi}{\gamma_0L_{\widehat{\mathcal S}}}\Bigr)\Big/\log\delta\Bigr\rceil_+.
--   $$
--
--   This is the $O(\log\epsilon^{-1})$ complexity of the strongly monotone case, and it is applied to each subproblem of Algorithm 2.
--
--   **Formalization Note** The statement has the shape of the goal: valid pairs exist, for every valid pair a terminated run exists, and every terminated run satisfies the bounds.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
--   - encoding: number of evaluations of $F$ and resolvent of $B$ → $\sum_t (n_t+1)$ over the iterations of the run, one number for both; reason: this is the count fixed by Remark 1(iii), p.5, and the proof of Theorem 2, p.19
--   - encoding: $\lceil\omega\rceil_+$ → `Nat.ceil`; reason: $(\lceil\omega\rceil)_+$ is the natural-number ceiling, for every real $\omega$
--   - generalization: $L_{\mathcal S},L_{\widehat{\mathcal S}}$ are the constants given by Lemma 1, for some choice → every pair valid in the sense of Lemma 1; reason: the proof uses only the two Lipschitz bounds, and Lemma 1 supplies such a pair, so the printed statement is the instance at that pair
--   - encoding: Algorithm 1 terminates and outputs $x^{t+1}$ within $T$ iterations → a terminated run `Alg1.Stops` exists, and every terminated run stops at an iteration `last` $\le T$ with output $x^{\mathrm{last}+1}$; reason: the run is relational and deterministic ($n_t$ least, $J$ a function); existence plus the bound on every terminated run is the printed claim
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Theorem 2, p.6

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Theorem 2.** arXiv:2206.00973v3, Theorem 2, p.6. Under the standing assumptions of §2,
Algorithm 1 terminates and outputs an `ε`-residual solution of (1) in at most `T` iterations, with
at most `N` evaluations of `F` and of the resolvent of `B`, where `T` is (12) and `N` is (13).

**Formalization Note.** The first clause is Lemma 1. The bounds hold for every valid pair
`L_S, L_Ŝ`, and a terminated run exists: runs are relational, so the second part alone would say
nothing. `T`, `N` depend on `x∗` through `r0`. The count is `opCount`, the same number for `F` and
for the resolvent. -/
theorem theorem_2 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg1.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg1.Standing B I xstar) :
    (∃ LS LShat : ℝ, Alg1.ValidS B I xstar LS LShat) ∧
    ∀ LS LShat : ℝ, Alg1.ValidS B I xstar LS LShat →
      (∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (n' : ℕ → ℕ) (last : ℕ),
        Alg1.Stops I x γ n' last) ∧
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (n' : ℕ → ℕ) (last : ℕ),
        Alg1.Stops I x γ n' last →
          last ≤ I.Tconst (I.r0 xstar) LS LShat ∧
          IsResidualSolution I.F B I.ε (x (last + 1)) ∧
          Alg1.opCount n' last ≤ I.Nconst (I.r0 xstar) LS LShat := by sorry

end MonoIncExtrap
