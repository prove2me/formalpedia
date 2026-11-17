-- Prove2me | Theorems.Thm_NearOptOWF_Supplement_theorem_5_2
-- name    : NearOptOWF.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:14:43.759822+00:00
-- url     : https://prove2.me/theorems/36fdb9cc-2c7e-4ad7-9c0a-3c19a0a43ee4
-- title:
--   Theorem 5.2 — $(\mu\cdot 4^{tr})$-secure output-intractable hash functions from iO and $\mathsf{NP}[r]\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$
-- statement:
--   Let $r,t:\mathbb N\to\mathbb N$ with $\omega(\log n)\le r\le o(n)$ and $t = \mathrm{poly}(n)$, and let the output length $m(n)$ be polynomially bounded and polynomial-time computable. Assume
--
--   1. $\mathsf{NP}[r]\not\subseteq_{\mathrm{i.o.}}\mathsf{coAM}$, where $\mathsf{NP}[r]$ is the set of NP languages with certificate length at most $r$, and
--   2. there exists a sub-exponentially secure indistinguishability obfuscator.
--
--   Then there is an efficiently sampleable hash function family $\mathcal H = \{f:\{0,1\}^n\to\{0,1\}^{m}\}$ such that for **every** $t$-ary relation ensemble $\mathcal R$, of density
--   $$
--   \mu = \Pr_{y_1,\dots,y_t\leftarrow\{0,1\}^m}\bigl[(y_1,\dots,y_t)\in\mathcal R\bigr],
--   $$
--   $\mathcal H$ is $(\mu\cdot 4^{tr})$-secure $\mathcal R$-output intractable against PPT adversaries: every PPT $A$ satisfies, for all sufficiently large $n$,
--   $$
--   \Pr_{f\leftarrow\mathcal H}\Bigl[x_i\ne x_j\ \text{for all}\ i\ne j\ \text{and}\ (f(x_1),\dots,f(x_t))\in\mathcal R : A(f)\to(x_1,\dots,x_t)\Bigr]\le \mu\cdot 4^{t r}.
--   $$
--
--   The family is fixed before the relation, which may be arbitrary, including inefficient. Collision resistance is the case $t = 2$ with $\mathcal R$ the equality relation.
--
--   Differences from the source:
--   - encoding: ω(log n) ≤ r ≤ o(n), t = poly(n) → r(n)/log n → ∞, r(n)/n → 0, and t(n) ≤ q(n) for a polynomial q; reason: the standard meaning of the asymptotic notation
--   - reading: hash family {0,1}^n → {0,1}^m with m unspecified → for every polynomially bounded, polynomial-time computable m (IsPolyLen), as in the base goal; reason: the construction sets λ = poly(n, m, t), so m is polynomial; quantifying over all such m is the strongest reading and matches the base Theorem 4.1
--   - reading: for sufficiently large n and m → for all sufficiently large n, with m = m(n); reason: m is a function of n; when m(n) → ∞ the two agree, otherwise the Lean bound is the stronger one
--   - generalization: ensemble R = {R_m ⊆ ({0,1}^m)^t} indexed by m → R n ⊆ ({0,1}^{m(n)})^{t(n)} indexed by n; reason: t is a function of n; every ensemble indexed by m gives one indexed by n via R n = R_{m(n)}, so the Lean statement specializes to the source's
--   - encoding: A(1^λ, H_k) → (x_1, …, x_t) → A run on (1^n, code of f), its output of length exactly t(n)·n split into n-bit blocks (oiProb); reason: λ = poly(n, m, t) is the construction's own parameter; a wrongly sized output fails
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2 and Definition 5.1, p.23 (PDF p.25); proof with Claims 5.6–5.8, pp.25–29

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_NPrNotSubsetIoCoAM
import Definitions.Def_NearOptOWF_SubexpIOExists
import Definitions.Def_NearOptOWF_FunFamily_IsEfficient
import Definitions.Def_NearOptOWF_Inverter_IsPPT
import Definitions.Def_NearOptOWF_IsPolyLen
import Definitions.Def_NearOptOWF_Supplement_relDensity
import Definitions.Def_NearOptOWF_Supplement_oiProb

namespace NearOptOWF.Supplement

/-- **Theorem 5.2** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Theorem 5.2, p.23 (PDF p.25)): let `ω(log n) ≤ r ≤ o(n)` and `t = poly(n)`,
and let the output length `m` be polynomially bounded and polynomial-time computable. Assume
`NP[r] ⊄_{i.o.} coAM` and that a sub-exponentially secure indistinguishability obfuscator exists. Then
there is one efficiently sampleable hash family `H = {f : {0,1}ⁿ → {0,1}^{m(n)}}` such that for **every**
`t`-ary relation ensemble `R` (arbitrary, possibly inefficient) of density `µ`, every PPT adversary `A`
satisfies, for all sufficiently large `n`,
`Pr[A(f) outputs pairwise distinct x₁, …, x_t ∈ {0,1}ⁿ with (f(x₁), …, f(x_t)) ∈ R] ≤ µ · 4^{t·r}`.

**Formalization Note** `ω(log n) ≤ r` is `r(n)/log n → ∞` and `r ≤ o(n)` is `r(n)/n → 0`. The family is
chosen before `R` and `A`. The output length `m` is read as in the base goal (`IsPolyLen`). Definition 5.1's
"sufficiently large `n` and `m`" is read as all sufficiently large `n`, with `m = m(n)`. -/
theorem theorem_5_2 (r t m : ℕ → ℕ)
    (hr_lo : Filter.Tendsto (fun n : ℕ => (r n : ℝ) / Real.log n) Filter.atTop Filter.atTop)
    (hr_hi : Filter.Tendsto (fun n : ℕ => (r n : ℝ) / n) Filter.atTop (nhds 0))
    (ht : ∃ q : Polynomial ℕ, ∀ n, t n ≤ q.eval n) (hm : IsPolyLen m)
    (hNP : NPrNotSubsetIoCoAM r) (hIO : SubexpIOExists) :
    ∃ H : FunFamily m, H.IsEfficient ∧
      ∀ (R : (n : ℕ) → Set (Fin (t n) → Fin (m n) → Bool)) (A : Inverter), A.IsPPT →
        ∀ᶠ n : ℕ in Filter.atTop,
          oiProb H t R A n ≤ relDensity m t R n * (4 : ℝ) ^ (t n * r n) := by sorry

end NearOptOWF.Supplement
