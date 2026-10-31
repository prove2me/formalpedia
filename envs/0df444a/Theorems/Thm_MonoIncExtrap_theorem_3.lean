-- Prove2me | Theorems.Thm_MonoIncExtrap_theorem_3
-- name    : MonoIncExtrap.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:04.882205+00:00
-- url     : https://prove2.me/theorems/3fc8c962-260f-4d35-bc69-38114aa10501
-- title:
--   Theorem 3, pp.7–8 — Algorithm 2 finds an $\varepsilon$-residual solution within $K+1$ iterations and $\bar M$ evaluations
-- statement:
--   Assume the standing assumptions of §3: $\varepsilon>0$, $\gamma_0>0$, $z^0\in\mathrm{dom}\,B$, $0<\delta<1$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\rho_0\ge1$, $0<\tau_0\le1$, $\zeta>1$, $0<\sigma<1/\zeta$, Assumption 1 with $\mu=0$, and let $x^*$ be an arbitrary fixed solution of (1). Let $L_{\mathcal Q},L_{\widehat{\mathcal Q}}$ be as in Lemma 2, $\xi=\nu(1-\eta)-\eta$, $\bar r_0=\|z^0-x^*\|$, and
--   $$
--   \Lambda=\frac{\rho_0\tau_0}{1-\sigma\zeta},\qquad C_1=\log\Bigl(\frac{(\bar r_0+\Lambda)(8+12\gamma_0L_{\mathcal Q})}{3\tau_0\sqrt{1-2\nu^2}\min\{L_{\widehat{\mathcal Q}}^{-1}\delta\xi,\gamma_0\}}\Bigr),
--   $$
--   $$
--   C_2=\Bigl\lceil\log\Bigl(\frac{\xi}{\gamma_0L_{\widehat{\mathcal Q}}}\Bigr)\Big/\log\delta\Bigr\rceil_+,\qquad C_3=\frac{1}{(\zeta-1)\log\bigl(1+\frac{2}{\rho_0(1-\eta)}\min\{L_{\widehat{\mathcal Q}}^{-1}\delta\xi,\gamma_0\}\bigr)}.
--   $$
--   Then Algorithm 2 terminates and outputs an $\varepsilon$-residual solution of (1) in at most $K+1$ iterations, and the number of evaluations of $F$ and of the resolvent of $B$ is at most $\bar M$, where
--   $$
--   K=\Bigl\lceil\max\Bigl\{\log_\zeta\Bigl(\frac{2\bar r_0+2\Lambda}{\varepsilon\rho_0}\Bigr),\frac{\log(2\tau_0/\varepsilon)}{\log(1/\sigma)}\Bigr\}\Bigr\rceil_+,
--   $$
--   and, with $W=\max\bigl\{\frac{2\zeta(\bar r_0+\Lambda)}{\varepsilon\rho_0},\ \zeta(\frac{2\tau_0}{\varepsilon})^{\frac{\log\zeta}{\log(1/\sigma)}},\ 1\bigr\}$,
--   $$
--   \bar M=8+C_2+(8+C_2)K+4\zeta(C_1)_+C_3W+4\zeta C_3(\log\sigma^{-1})KW.
--   $$
--
--   This is the paper's main result: $\bar M=O(\varepsilon^{-1}\log\varepsilon^{-1})$ for problem (1) with $F$ only locally Lipschitz and $\mathrm{dom}\,B$ possibly unbounded, improving the previous $O(\varepsilon^{-2})$.
--
--   **Formalization Note** In order, the theorem asserts: valid pairs exist (Lemma 2); for every valid pair a terminated run of Algorithm 2 exists; and every terminated run stops at outer iteration `last` $\le K$, with an $\varepsilon$-residual output and total count at most $\bar M$. Outer iterations are $0,\dots,$ `last`, so `last` $\le K$ is "at most $K+1$ iterations". The paper's name $W$ is not used; `maxTerm` is this maximum.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
--   - generalization: $\mu=0$, i.e. $F+B$ is monotone but not strongly monotone on $\mathrm{dom}\,B$ → Assumption 1(b) with $\mu=0$, without the "not strongly monotone" clause; reason: the proof never uses the failure of strong monotonicity (Remark 4(iii)); the printed case is a special case
--   - generalization: $L_{\mathcal Q},L_{\widehat{\mathcal Q}}$ are the constants given by Lemma 2, for some choice → every pair valid in the sense of Lemma 2; reason: the proof uses only the two Lipschitz bounds, and Lemma 2 supplies such a pair, so the printed statement is the instance at that pair
--   - encoding: number of evaluations of $F$ and resolvent of $B$ → $\sum_t (n_t+1)$ over the iterations of the run, one number for both; reason: this is the count fixed by Remark 1(iii), p.5, and the proof of Theorem 2, p.19
--   - encoding: $\lceil\omega\rceil_+$ → `Nat.ceil`; reason: $(\lceil\omega\rceil)_+$ is the natural-number ceiling, for every real $\omega$
--   - encoding: Algorithm 2 terminates and outputs $z^{k+1}$ within $K+1$ iterations → a terminated run `Alg2.Stops` exists, and every terminated run stops at outer iteration `last` $\le K$ with output $z^{\mathrm{last}+1}$; reason: outer iterations are $0,\dots,$`last`; the run is relational and deterministic, so existence plus the bound on every terminated run is the printed claim
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Theorem 3, pp.7–8

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1
import Definitions.Def_MonoIncExtrap_Algorithm2

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Theorem 3.** arXiv:2206.00973v3, Theorem 3, pp.7–8. Under the standing assumptions of §3 (in
particular `μ = 0`), Algorithm 2 terminates and outputs an `ε`-residual solution of (1) in at most
`K + 1` iterations, and the number of evaluations of `F` and of the resolvent of `B` is at most `M̄`,
where `K` is (20) and `M̄` is (21).

**Formalization Note.** The first clause is Lemma 2. The bounds hold for every valid pair
`L_Q, L_Q̂`, and a terminated run exists: runs are relational, so the bounds alone would say nothing.
"At most `K + 1` iterations" is `last ≤ K`, since outer iterations are `0, …, last`. `K` and `M̄`
depend on the fixed solution `xstar` through `r̄0`, and on `L_Q, L_Q̂`, which do not depend on `ε`.
`F` is only locally Lipschitz and `dom B` may be unbounded. The count is the sum of the inner
`Σ(n_t + 1)`, the same number for `F` and for the resolvent. -/
theorem theorem_3 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg2.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg2.Standing B I xstar) :
    (∃ LQ LQhat : ℝ, Alg2.ValidQ B I xstar LQ LQhat) ∧
    ∀ LQ LQhat : ℝ, Alg2.ValidQ B I xstar LQ LQhat →
      (∃ (z : ℕ → EuclideanSpace ℝ (Fin n)) (c : ℕ → ℕ) (last : ℕ), Alg2.Stops I z c last) ∧
      ∀ (z : ℕ → EuclideanSpace ℝ (Fin n)) (c : ℕ → ℕ) (last : ℕ),
        Alg2.Stops I z c last →
          last ≤ I.Kconst (I.rbar xstar) ∧
          IsResidualSolution I.F B I.ε (z (last + 1)) ∧
          ((∑ k ∈ Finset.range (last + 1), c k : ℕ) : ℝ) ≤
            I.Mbar (I.rbar xstar) LQ LQhat := by sorry

end MonoIncExtrap
