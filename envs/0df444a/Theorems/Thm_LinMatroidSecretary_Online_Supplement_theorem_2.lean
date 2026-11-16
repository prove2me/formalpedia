-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_Supplement_theorem_2
-- name    : LinMatroidSecretary.Online.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:25.521209+00:00
-- url     : https://prove2.me/theorems/4986b19d-f5ca-49c8-88a0-77072951798b
-- title:
--   Theorem 2 — 1/e expected welfare in both XOS secretary models
-- statement:
--   Let $E$ be a finite labelled set of items and $N=\{0,\ldots,n-1\}$ the agents. Each agent $a$ has an eligibility set $E_a\subseteq E$ and an XOS valuation $f_a$ on its subsets, fixed before agents arrive in uniformly random order. Allocated bundles must be eligible and pairwise disjoint, with independent union. There exist online algorithms with both of the following guarantees.
--
--   1. For every known linear matroid $M$ on $E$, representable over any field, and every $n$, a policy can be chosen as a function of $M,E,n$ before any agent data are given. It sees only revealed eligibility sets, their valuations, and its own past assignments.
--   2. For every known finite field $F$, dimension $d$, $n$ and finite ground type $E$, one policy can be chosen before the representation $v:E\to F^d$ and before the agent data. It additionally observes only the vectors of revealed eligible elements, in the common coordinate system.
--
--   In each model, for every XOS instance, every positive-probability run produces a feasible allocation, and for every feasible offline allocation $T^*$,
--   $$\mathbb E[F(\mathrm{ALG})]\ge\exp(-1)\sum_{a\in N}f_a(T^*_a)=\frac1e F(T^*).$$
--   Thus the bound holds for the offline optimum. Every $n$ is covered, including $n=1,2$; there is no sample-size or large-$n$ restriction. Expectations average the uniform arrival order and the policy's internal randomness. This companion result extends the mission to agent arrivals and XOS welfare and is not used to prove the retained goal Theorem 1.
--
--   Differences from the source:
--   - encoding: online randomized decisions on the information revealed so far → behavioural probability distributions on bundles, queried on histories of eligibility sets, their subset valuations, restricted revealed vectors and previous assigned bundles; reason: finite-horizon perfect-recall decisions admit behavioural kernels; no agent indices, future data, outside values or unseen vectors are inputs; policies are chosen before instances and, in the online clause, before representations
--   - encoding: comparison with F(OPT(N)) → comparison with F(T*) for every feasible allocation T*; reason: finitely many allocations exist and the empty allocation is feasible, so the offline maximum is attained
--   - encoding: finite labelled items and agents, finite-dimensional representations, and the constant 1/e → finite types E, agents Fin n, coordinates Fin d, arbitrary-field representability for the known clause, and Real.exp (-1); reason: finite reindexing and coordinates preserve the model, including n=1,2 and the empty-agent case; exp(-1)=1/e
--   - encoding: XOS valuations defined only on eligible subsets → the published XOS predicate on D ↦ f_a(D ∩ E_a); reason: nonnegative clauses extend by zero outside E_a and restrict back, so this neither restricts nor reveals any additional valuation data
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, Theorem 2, PDF p. 21 (printed p. 19)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Supplement_Allocation

namespace LinMatroidSecretary.Online.Supplement

/-- Theorem 2, STOC 2027 #608, PDF p. 21 (printed p. 19), both information models.
In each clause the policy is chosen before the agents' eligibility sets and valuations;
in the second it is also chosen before the vector representation. Comparison against
every feasible allocation is equivalent to comparison against the attained offline optimum. -/
theorem theorem_2 :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (M : Matroid E),
      M.E = Set.univ → IsLinear M → ∀ n : ℕ,
      ∃ π : AllocationPolicy E Unit n, π.Valid ∧
        ∀ I : Instance E n, I.Valid →
          AlwaysFeasible M π I (fun _ => ()) ∧
          ∀ Tstar : Fin n → Finset E, Feasible M I Tstar →
            Real.exp (-1) * welfare I Tstar ≤ expectedWelfare π I (fun _ => ())) ∧
    (∀ (F : Type) [Field F] [Fintype F] (d n : ℕ)
      (E : Type) [Fintype E] [DecidableEq E],
      ∃ π : AllocationPolicy E (Fin d → F) n, π.Valid ∧
        ∀ (v : E → Fin d → F) (I : Instance E n), I.Valid →
          AlwaysFeasible (linMatroid (F := F) v) π I v ∧
          ∀ Tstar : Fin n → Finset E, Feasible (linMatroid (F := F) v) I Tstar →
            Real.exp (-1) * welfare I Tstar ≤ expectedWelfare π I v) := by sorry

end LinMatroidSecretary.Online.Supplement
