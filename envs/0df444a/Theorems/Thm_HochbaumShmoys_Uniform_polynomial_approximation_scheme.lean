-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_polynomial_approximation_scheme
-- name    : HochbaumShmoys.Uniform.polynomial_approximation_scheme
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:23.05499+00:00
-- url     : https://prove2.me/theorems/1516988e-7b4f-4157-8813-e352e34f9d3f
-- title:
--   Binary search over all-pack is a polynomial approximation scheme for makespan on uniform machines (Abstract, p. 539; Corollary 1, p. 541, with §3)
-- statement:
--   For every $\varepsilon>0$ there are an integer $N\ge2$ (the parameter $\delta=1/N$ at which all-pack is run) and natural numbers $C,d$, all depending only on $\varepsilon$, such that for every instance of the minimum makespan problem on uniform machines, with $m\ge1$ machines of speeds $s_i>0$ and $n$ jobs of processing times $p_j>0$:
--
--   1. **Approximation.** For every resolution $D$ of all-pack at $\delta=1/N$ (every way of making its arbitrary choices), the schedule $\sigma^\ast$ output by the binary search of §2 driven by $D$ and run for $\lceil\log_2 m+\log_2(3/\varepsilon)\rceil$ iterations satisfies, for every schedule $\tau$,
--   $$C_{\max}(\sigma^\ast)\le(1+\varepsilon)\,C_{\max}(\tau);$$
--   2. **Polynomial size.** For every deadline $T>0$ and every ordering of the bins $Ts_1,\dots,Ts_m$ by non-increasing size, the layered graph that all-pack builds for the deadline-$T$ instance (pieces $p_j$, bins $Ts_i$, normalized by the largest bin) has at most
--   $$C\cdot m\cdot(n+1)^d$$
--   arcs.
--
--   This is the paper's main result: a family of polynomial-time algorithms $\{A_\varepsilon\}$, $A_\varepsilon$ delivering a schedule within relative error $\varepsilon$ of the optimum (a polynomial approximation scheme for $Q\|C_{\max}$), polynomial in the input size for fixed $\varepsilon$ though not in $1/\varepsilon$.
--
--   **Formalization Note** The paper states the scheme in words (Abstract; §1) and obtains it from Corollary 1 with all-pack; there is no numbered statement. Running time is measured, as in Theorem 2, by the size of the graph all-pack builds (each step is an arc evaluation or an update); the binary search makes $\lceil\log_2m+\log_2(3/\varepsilon)\rceil$ calls. The constants $N,C,d$ are chosen after $\varepsilon$ and before the instance, so they cannot depend on $m,n,p,s$; $n+1$ replaces $n$ so the bound is meaningful for $n=0$. The algorithm is the binary search with the concrete procedure all-pack, not an arbitrary relaxed decision procedure, and the guarantee holds for every resolution of all-pack's choices. The exponent $10/\varepsilon^2+3$ of Theorem 2 is not asserted (findings F2, F3).
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, Abstract, p. 539, and §2–§3, Corollary 1 (p. 541) with Theorem 2 (p. 549)

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_BinarySearch
import Definitions.Def_HochbaumShmoys_Uniform_AllPack

namespace HochbaumShmoys.Uniform

theorem polynomial_approximation_scheme :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∃ C d : ℕ,
      ∀ (m n : ℕ) (hm : 0 < m) (s : Fin m → ℝ) (p : Fin n → ℝ),
        (∀ i, 0 < s i) → (∀ j, 0 < p j) →
        (∀ D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m),
          IsAllPackResolution N D → ∀ τ : Fin n → Fin m,
            makespan p s (binarySearch D p s hm (iterationCount m ε)) ≤
              (1 + ε) * makespan p s τ) ∧
        (∀ T : ℝ, 0 < T → ∀ ord : Fin m ≃ Fin m, Antitone (fun t => T * s (ord t)) →
          arcCount N (normalizedBins (fun i => T * s i) ord)
              (normalizedPieces p (fun i => T * s i)) ≤ C * m * (n + 1) ^ d) := by sorry

end HochbaumShmoys.Uniform
