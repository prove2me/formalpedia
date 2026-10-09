-- Prove2me | Theorems.Thm_IntMul_HvdH_corollary_5_5
-- name    : IntMul.HvdH.corollary_5_5
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T00:11:36.564505+00:00
-- url     : https://prove2.me/theorems/d6324285-9226-45cc-9555-a7ffbfa4fcf7
-- title:
--   Corollary 5.5 — $\mathsf T(n)<\frac{1728}{d-1/2}\mathsf T(3rp)+O(1)$ for the recursive multiplication algorithm
-- statement:
--   **Corollary 5.5 of Harvey–van der Hoeven.** Fix a dimension parameter $d\ge2$ and put $n_0=2^{d^{12}}$. For $n\ge n_0$, the parameters of §5.1 are:
--
--   - $b=\lceil\log_2 n\rceil$ and $p=6b$;
--   - $T$, the unique power of two with $4n/b\le T<8n/b$;
--   - $r$, the unique power of two with $T^{1/d}\le r<2T^{1/d}$.
--
--   There is a deterministic multitape Turing machine $M$, correct on all $n$-bit inputs for every $n\ge1$, with worst-case running time $\mathsf M(n)$, and a constant $A$, such that for every $n\ge n_0$, with $\mathsf T(n):=\mathsf M(n)/(n\log n)$,
--   $$\mathsf T(n)<\frac{1728}{d-\frac12}\,\mathsf T(3rp)+A .$$
--
--   Here $\log$ is the natural logarithm. Taking $d=1729$, the factor is below $0.9998$, and an induction on $n$ then gives $\mathsf T(n)=O(1)$, that is, Theorem 1.1, $\mathsf M(n)=O(n\log n)$. In the paper this corollary follows from Proposition 5.4, $\mathsf M(n)<\frac{12T}{r}\mathsf M(3rp)+O(n\log n)$, the recursive step of the algorithm.
--
--   **Formalization Note** The machine model is `IntMul_MultitapeModel`. $\mathsf M(n)$ is $\inf\{\tau:\mathrm{MultipliesAt}(M,n,\tau)\}$, which is exactly $M$'s worst-case halting time on pairs of $n$-bit inputs. The parameters $b,p,T,r$ are universally quantified under their defining conditions, and these conditions determine them uniquely. The paper's $\mathsf M$ is the running time of its specific algorithm. The statement asserts the existence of a correct machine satisfying the recurrence, which is what the paper establishes for that algorithm.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), Corollary 5.5, p. 41; parameters from §5 (n0 = 2^{d^12}), (5.1) b, (5.2) p, (5.6) T, (5.7) r, pp. 36-37

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.HvdH

theorem corollary_5_5 (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ A : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r → (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} / ((n : ℝ) * Real.log n) <
            1728 / ((d : ℝ) - 1 / 2) *
              (sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} /
                (((3 * r * p : ℕ) : ℝ) * Real.log ((3 * r * p : ℕ) : ℝ))) + A := by sorry

end IntMul.HvdH
