-- Prove2me | Theorems.Thm_OAI_EuclideanSteinitz_Filter_applicationDomain_survival
-- name    : OAI.EuclideanSteinitz.Filter.applicationDomain_survival
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:21:16.156989+00:00
-- url     : https://prove2.me/theorems/d57bffdc-d011-4430-93de-05bd456548f7
-- title:
--   Uniform Gaussian survival in the filtered application body (OpenAI Euclidean Steinitz–Bergström)
-- statement:
--   Let $\iota$, $\kappa$, $T$, $J$ be finite types, $\iota$ and $\kappa$ nonempty with decidable equality. All definitions below are OpenAI's, from the definitions bundle `OAIQWESB000` of this split.
--
--   **Steps and runs.** A step `p : Step ι κ` consists of a matrix $C \in \mathbb R^{\iota\times\iota}$, a vector $b \in \mathbb R^\iota$ and a column index $j \in \kappa$. It is good (`Step.Good`) if $C$ is invertible and $CC^{\mathsf T} + bb^{\mathsf T} = I$. It acts on $R \in \mathbb R^{\iota\times\kappa}$ by $R \mapsto CR + b\,e_j^{\mathsf T}$ (`Step.apply`), and `run R ps` applies the steps of a list `ps` in order. A list $L$ is fresh for $R$ (`Fresh R L`) if $R_{i,p.j} = 0$ for every step $p$ of $L$ and every $i$.
--
--   **The body.** For $B \in \mathbb R^{\alpha\times\beta}$, `matrixMap B` is the linear map $x \mapsto Bx$ between the Euclidean spaces, and `squareMass B` $= \sum_{i,j} B_{ij}^2$. For a family $R_t \in \mathbb R^{\iota\times\kappa}$ ($t \in T$) and rows $H_j \in \mathbb R^{1\times\kappa}$ ($j \in J$), `applicationDomain R H` $\subseteq \mathbb R^\kappa$ is the set of $x$ with
--   $$\|R_t x\| < 2\,\mathtt{stateRadius}\sqrt{|\iota|}\ \ (t \in T),\qquad \|x\| < 2\,\mathtt{stateRadius}\sqrt{|\kappa|},\qquad \|H_j x\| < 2\,\mathtt{slabRadius}\ \ (j \in J),$$
--   where `stateRadius` and `slabRadius` are positive absolute constants of the bundle; `bodyRate` $= 2\,\mathtt{stateRate} + 1$ is another.
--
--   **The Gaussian chain.** For $r \in \mathbb R^\kappa$, $n \in \mathbb N$ and $u \le n$, `evaluation r n u` $\in \mathbb R^{\kappa \times ((n+1)\times\kappa)}$ has entries $\mathtt{row}(r_i, u, k)$ in row $i$ and column $(k, i)$, and $0$ elsewhere, where $\mathtt{row}(r, 0, k) = [k = 0]$ and $\mathtt{row}(r, u+1, k) = r\,\mathtt{row}(r, u, k) + [k = u+1]\sqrt{1-r^2}$. Applied to a standard Gaussian vector $x$ of $\mathbb R^{(n+1)\times\kappa}$, the values $X_u = $ `evaluation r n u` $x$, $u = 0, \dots, n$, form a stationary Gaussian autoregressive chain with independent coordinates, $X_{u+1,i} = r_i X_{u,i} + \sqrt{1-r_i^2}\,\xi_{u+1,i}$.
--
--   **Statement.** Let $R \in \mathbb R^{\iota\times\kappa}$ with $RR^{\mathsf T} = I$, let $L$ be a list of good steps that is fresh for $R$ and whose column indices are pairwise distinct (`(L.map Step.j).Nodup`), and let `ps : T → List (Step ι κ)` assign to each $t$ a prefix of $L$. Let $H_j \in \mathbb R^{1\times\kappa}$ ($j \in J$) satisfy `squareMass (H j) ≤ 1` for every $j$ and $\sum_j H_j(i)^2 \le 1$ for every column $i$. Let $q \in \mathbb R^\kappa$ with $q_i > 0$ for all $i$. Then there is $a \in \mathbb R$ such that for every $n \in \mathbb N$, with $\gamma$ the standard Gaussian measure on $\mathbb R^{(n+1)\times\kappa}$ (`stdGaussian`) and $r_i = (1+q_i)^{-1}$,
--   $$e^{-a - \mathtt{bodyRate}\,(\sum_i q_i)\,n} \;\le\; \gamma\Bigl\{x : \text{evaluation}(r, n, u)\,x \in \text{applicationDomain}\bigl(t \mapsto \text{run}(R, ps_t),\, H\bigr) \text{ for all } u \le n\Bigr\}.$$
--   This is the uniform survival bound behind Proposition 2.2 of OpenAI's paper: the survival exponent of the chain in the body grows at most linearly in $\sum_i q_i$, uniformly in the number of steps.
--
--   Lean: `OAI.EuclideanSteinitz.Filter.applicationDomain_survival`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Steinitz/FilteredBody.lean`). It is published as an intermediate statement of this split only because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf, Proposition 2.2 and Section 5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/FilteredBody.lean (declaration OAI.EuclideanSteinitz.Filter.applicationDomain_survival)

import Mathlib
import Definitions.Def_OAIQWESB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

lemma applicationDomain_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    (H : J → Matrix Unit κ ℝ) (hH : ∀ j,squareMass (H j)≤1) (hcol : ∀ i,∑ j,(H j () i)^2≤1)
    {q : κ → ℝ} (hq : ∀ i,0<q i) :
    ∃ a : ℝ,∀ n : ℕ,Real.exp (-a-bodyRate*(∑ i,q i)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
        {x | ∀ u : Fin (n+1),matrixMap (evaluation (fun i => (1+q i)⁻¹) n u) x ∈
          applicationDomain (fun t => run R (ps t)) H} := by
  sorry

end EuclideanSteinitz.Filter

end

end OAI
end
