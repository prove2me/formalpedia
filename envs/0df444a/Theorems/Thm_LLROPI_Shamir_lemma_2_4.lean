-- Prove2me | Theorems.Thm_LLROPI_Shamir_lemma_2_4
-- name    : LLROPI.Shamir.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:33:52.02578+00:00
-- url     : https://prove2.me/theorems/b590ab0a-6262-4678-87f4-5dd97336314f
-- title:
--   Lemma 2.4 (arc bound) — $|\widehat{1_S}(\xi)|\le\frac{\sin(\pi\rho)}{p\sin(\pi/p)}=\frac{\sin(\pi\rho)}{\pi}+O(p^{-2})$ for $\xi\ne0$
-- statement:
--   Let $p$ be a prime and $S\subseteq\mathbb F_p$ have size $|S|=\rho p$. Then for every $\xi\ne0$,
--   $$\big|\widehat{1_S}(\xi)\big|\le\frac{\sin(\pi\rho)}{p\sin(\pi/p)}=\frac{\sin(\pi\rho)}{\pi}+O(p^{-2}),$$
--   as $p\to\infty$ uniformly in $\rho$. Here $\hat f(\xi)=\mathbb E_xf(x)e_p(x\xi)$. In the formal statement the inequality holds for every prime $p$, and the $O(p^{-2})$ is a single constant $C$, chosen before $p$, $S$ and $\xi$, with $\big|\frac{\sin(\pi\rho)}{p\sin(\pi/p)}-\frac{\sin(\pi\rho)}{\pi}\big|\le C/p^2$.
--
--   Differences from the source:
--   - reading: as p → ∞ uniformly in ρ, … = sin(πρ)/π + O(p^{−2}) → one constant C chosen before p, S, ξ with |sin(πρ)/(p sin(π/p)) − sin(πρ)/π| ≤ C/p² for every prime p; reason: the uniform reading of O(·); finitely many small primes are absorbed into C
--   - reading: the inequality |1̂_S(ξ)| ≤ sin(πρ)/(p sin(π/p)), printed under "as p → ∞ uniformly in ρ" → stated for every prime p; reason: the phrase "as p → ∞" qualifies the O(p^{−2}) expansion; the arc bound itself is exact (the maximum of |Σ_{x∈S} e_p(xξ)| over |S| = ρp is attained by an arc), so the every-prime reading is the stronger one
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.4, p. 21 (PDF 23)

import Mathlib
import Definitions.Def_LLROPI_Shamir_Fourier

namespace LLROPI.Shamir

/-- **Lemma 2.4 (Arc Bound; see [SW26])**, p. 21 (PDF 23). Let `S ⊆ 𝔽_p` have size `|S| = ρp`.
Then for every `ξ ≠ 0`, as `p → ∞` uniformly in `ρ`,
`|1̂_S(ξ)| ≤ sin(πρ) / (p sin(π/p)) = sin(πρ)/π + O(p⁻²)`.
Sun, Wootters, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.4, p. 21 (PDF 23).

**Formalization Note.** The inequality is stated for every prime `p`. The `O(p⁻²)` is one constant
`C`, chosen before `p`, `S` and `ξ` (uniform in `ρ = |S|/p`). The Fourier transform is the
normalized one with a plus sign. -/
theorem lemma_2_4 :
    ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) (ξ : ZMod p), ξ ≠ 0 →
      ‖fourier (indicatorC S) ξ‖ ≤
          Real.sin (Real.pi * density S) / ((p : ℝ) * Real.sin (Real.pi / p)) ∧
        |Real.sin (Real.pi * density S) / ((p : ℝ) * Real.sin (Real.pi / p))
            - Real.sin (Real.pi * density S) / Real.pi| ≤ C / (p : ℝ) ^ 2 := by sorry

end LLROPI.Shamir
