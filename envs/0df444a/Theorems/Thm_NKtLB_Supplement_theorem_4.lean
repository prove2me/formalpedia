-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_4
-- name    : NKtLB.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:37:14.445288+00:00
-- url     : https://prove2.me/theorems/72cda809-b570-4e81-969d-c2a1dae15abb
-- title:
--   Theorem 4 — SoI for nKt or rnKt collapses FewEXP, $\mathsf{EXP}^{\|\mathsf{NP}}$ and $\mathsf{BPEXP}^{\|\mathsf{NP}}$
-- statement:
--   **Strong complexity collapses from symmetry of information.**
--
--   1. *(Uniform collapses.)* If SoI holds for $n\mathrm{Kt}$ or for $rn\mathrm{Kt}$ with error $e(n)=O(\log n)$, then $\mathsf{FewEXP}\subseteq\mathsf{BPP}^{\mathsf{NP}}$. If SoI holds for $n\mathrm{Kt}$ or for $rn\mathrm{Kt}$ with error $e(n)=\mathrm{poly}(\log n)$, then
--   $$
--   \mathsf{FewEXP}\subseteq\mathsf{BPTIME}^{\mathsf{NP}}[n^{\mathrm{poly}(\log n)}].
--   $$
--   2. *(Nonuniform collapses.)* If SoI holds for $rn\mathrm{Kt}$ with error $O(\log n)$, then $\mathsf{BPEXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}$. If SoI holds for $n\mathrm{Kt}$ with error $O(\log n)$, then
--   $$
--   \mathsf{EXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}.
--   $$
--
--   "SoI holds for $\mu$ with error $e(n)$" means $\mu(x,y)\ge\mu(x)+\mu(y\mid x)-e(n)$ for all $x,y\in\{0,1\}^n$ (p.5). Here $n\mathrm{Kt}$ is the nondeterministic Levin–Kolmogorov complexity of the base mission, $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$, and all measures are taken with respect to an arbitrary valid universal machine $U$.
--
--   By Part 2 and Yap's theorem, SoI for $n\mathrm{Kt}$ or $rn\mathrm{Kt}$ would collapse the polynomial hierarchy. The paper reads this as evidence that information is asymmetric for nondeterministic computation.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: SoI with error $e(n)=O(\log n)$ (p.5) → $\exists c>0\,\exists N\,\forall n\ge N$: SoI at length $n$ with error $c\log_2 n$; reason: an $O(\log n)$ bound constrains only large $n$; at $n\le1$ a literal $c\log n$ is $0$ and would demand exact additivity
--   - reading: SoI with error $e(n)=\mathrm{poly}(\log n)$ → $\exists c>0\,\exists N\,\forall n\ge N$: SoI at length $n$ with error $(\log_2 n)^c$; reason: standard meaning of $\mathrm{poly}(\log n)$, matching the explicit form of Theorems 59/65
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: $\mathsf C[n^{\mathrm{poly}(\log n)}]$ / $\mathsf C[n^{\mathrm{polylog}(n)}]$ → $\bigcup_{c\in\mathbb N}\mathsf C[\lceil n^{(\log_2 n)^c}\rceil]$; reason: the standard meaning of the class
--   - reading: non-adaptive (parallel) oracle access $\|$ → one round of `AdaptRounds` on every input and random string; reason: the paper gives no formal definition; this is the semantic one
--   - reading: oracle class NP in $\mathsf C^{\mathsf{NP}}$ → union over oracles $A\in\mathsf{NP}$; reason: standard meaning of relativization to a class
--   - reading: FewEXP: NEXP languages with $2^{\mathrm{poly}(n)}$ witnesses per positive instance (p.9) → verifier with witnesses of length exactly $2^{|x|^k}$, at most $2^{c|x|^k+c}$ accepted per input; reason: the paper's own normalization (Claim 76, p.48)
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_SoIAt
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_Supplement_FewEXP
import Definitions.Def_NKtLB_Supplement_NP
import Definitions.Def_NKtLB_Supplement_BPTIMEO
import Definitions.Def_NKtLB_Supplement_qpoly
import Definitions.Def_NKtLB_Supplement_BPEXPPar
import Definitions.Def_NKtLB_Supplement_EXPPar
import Definitions.Def_NKtLB_Supplement_NPpoly
import Definitions.Def_NKtLB_Supplement_coNPpoly

namespace NKtLB.Supplement

/-- **Theorem 4 (Strong Complexity Collapses from SoI)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9): "The following
results hold:
(i) [Uniform Collapses]
– If SoI holds for nKt or rnKt with error `e(n) = O(log n)`, then `FewEXP ⊆ BPP^{NP}`.
– If SoI holds for nKt or rnKt with error `e(n) = poly(log n)`, then `FewEXP ⊆ BPTIME^{NP}[n^{poly(log n)}]`.
(ii) [Nonuniform Collapses]
– If SoI holds for rnKt with error `e(n) = O(log n)`, then `BPEXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`.
– If SoI holds for nKt with error `e(n) = O(log n)`, then `EXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`."

**Formalization Note.** For every valid universal machine `U` (base readings R1, R2). "SoI holds
for `μ` with error `e(n) = O(log n)`" is `∃ c > 0, ∃ N, ∀ n ≥ N, SoIAt μ n (c·log₂ n)` and "with error
`e(n) = poly(log n)`" is `∃ c > 0, ∃ N, ∀ n ≥ N, SoIAt μ n ((log₂ n)^c)` (p.5 definition; an `O(·)`
bound constrains only large `n`). `nKt` is the base `nKt` with `O = ∅`, `rnKt = rnKt_{2/3}` (p.22). `BPP^{NP} = ⋃_k ⋃_{A ∈ NP} BPTIME^A[n^k]`,
`BPTIME^{NP}[n^{poly(log n)}] = ⋃_c ⋃_{A ∈ NP} BPTIME^A[n^{(log n)^c}]`, `EXP^{∥NP} = ⋃_{A ∈ NP} EXP^{∥A}`,
`BPEXP^{∥NP} = ⋃_{A ∈ NP} BPEXP^{∥A}`. -/
theorem theorem_4 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ((((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => nKt U ∅ ⊤ x y []) n (c * Real.logb 2 n)) ∨ (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => rnKt U ∅ (2 / 3) x y) n (c * Real.logb 2 n))) →
      FewEXP ⊆ {L | ∃ k : ℕ, ∃ A ∈ NP, L ∈ BPTIMEO A (fun n => n ^ k)}) ∧
    (((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => nKt U ∅ ⊤ x y []) n (Real.logb 2 n ^ c)) ∨ (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => rnKt U ∅ (2 / 3) x y) n (Real.logb 2 n ^ c))) →
      FewEXP ⊆ {L | ∃ c : ℕ, ∃ A ∈ NP, L ∈ BPTIMEO A (qpoly c)})) ∧
    ((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => rnKt U ∅ (2 / 3) x y) n (c * Real.logb 2 n)) →
      {L | ∃ A ∈ NP, L ∈ BPEXPPar A} ⊆ NPpoly ∩ coNPpoly) ∧
    ((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => nKt U ∅ ⊤ x y []) n (c * Real.logb 2 n)) →
      {L | ∃ A ∈ NP, L ∈ EXPPar A} ⊆ NPpoly ∩ coNPpoly) := by sorry

end NKtLB.Supplement
