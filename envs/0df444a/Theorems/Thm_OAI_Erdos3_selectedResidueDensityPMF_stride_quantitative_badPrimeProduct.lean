-- Prove2me | Theorems.Thm_OAI_Erdos3_selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
-- name    : OAI.Erdos3.selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T07:01:51.197074+00:00
-- url     : https://prove2.me/theorems/858e73dd-7180-4db9-aa21-9613b162fc2f
-- title:
--   Joint bad-prime bounds make a large tested bad prime product rare under the residue law
-- statement:
--   Let $K$, $I$ be finite types, $\mathrm{modulus} : I \to \mathbb{N}$, and $G$ a finite set of column residue patterns (`ColumnResiduePattern K I modulus`, i.e. elements of $\prod_{(k,i)} \mathbb{Z}/\mathrm{modulus}_i$). Let $V : K \times I \to \mathbb{R}$ with all values positive, and let $w(x) = $ `selectedResidueSmoothWeight modulus G V x` for $x \in \mathbb{Z}^{K \times I}$: this is $\prod_z \phi(x_z/V_z)$ (with $\phi$ OpenAI's smooth probability profile) if the residue pattern of $x$ lies in $G$, and $0$ otherwise; assume $\sum_x w(x) > 0$. Let $D : \mathbb{Z}^{K \times I} \to \mathbb{R}$ with $D \ge 0$ and `selectedResidueDensityMass modulus G V D` $= \sum_x \frac{w(x)}{\sum_y w(y)}D(x) > 0$, and let $\mu$ = `selectedResidueDensityPMF modulus G V hV hZ D hD0 hD`, the probability mass function on $\mathbb{Z}^{K \times I}$ proportional to $w(x)D(x)$. Let $S$ be a finite set of primes, $A : \mathbb{N} \to \mathbb{N}$, $\mathrm{bad} : \mathbb{N} \to \mathbb{N} \to \mathbb{Z}^{K \times I} \to \mathrm{Prop}$, and $\mathrm{stride}, Q_s, Q \in \mathbb{N}$ with $\mathrm{stride} > 0$, $Q_s \ge 2$, $Q \ge 1$ and $p^{A(p)} \le Q$ for all $p \in S$. Let $E, V_{\log} \ge 0$ be real with $Q \le e^{V_{\log}}$. Put $R = $ `quantitativeBadPrimeRadius E` $= \lceil 4e^{E}\rceil_{\mathbb{N}} + 1$ and $\eta = e^{-E}/(2(Q + R^2))$. Assume (hypothesis `hjoint`) that for every $T \subseteq S$ and every $a : \mathbb{N} \to \mathbb{N}$ such that each $p \in T$ has $0 < a(p) \le A(p)$, $Q_s \le p^{a(p)}$ and $2\,v_p(\mathrm{stride}) < a(p)$ ($v_p$ the $p$-adic valuation), and $\prod_{p \in T} p^{a(p)} \le \max(Q, R^2)$, the $\mu$-probability that $\mathrm{bad}(p, a(p), x)$ holds for all $p \in T$ is at most $1/(\prod_{p \in T} p^{a(p)})^{10} + \eta$. Then $0 < R$, $R \le e^{E+3}$, $0 < \eta$, $\max(Q, R^2) \le e^{V_{\log} + 2E + 6}$, $\eta^{-1} \le e^{V_{\log} + 3E + 8}$, and the $\mu$-probability of the event
--   $$\mathrm{stride}^2\cdot\texttt{smallPrimePowerCorrection}(Q_s)\cdot R < \prod_{p \in S} p^{\,\texttt{largestTestedBadDepth}\ A\ \mathrm{bad}\ p\ x}$$
--   is at most $e^{-E}$. Here `smallPrimePowerCorrection Qs` $= \prod_{p < Q_s \text{ prime}} p^{\lfloor \log_p(Q_s - 1)\rfloor}$ and `largestTestedBadDepth A bad p x` is the largest $a \in [1, A(p)]$ with $\mathrm{bad}(p, a, x)$ (and $0$ if there is none).
--
--   Lean: `OAI.Erdos3.selectedResidueDensityPMF_stride_quantitative_badPrimeProduct` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedCertifiedPhysicalBadProduct.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B049` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedCertifiedPhysicalBadProduct.lean#L14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B049

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {stride Qs Q : ℕ} (hstride : 0 < stride)
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {E Vlog : ℝ} (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hjoint :
      let R := quantitativeBadPrimeRadius E
      let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
      ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
        (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧
          2 * stride.factorization p < a p) →
        (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
        (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
          (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
          1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < R ∧ (R : ℝ) ≤ Real.exp (E + 3) ∧ 0 < η ∧
      ((max Q (R ^ 2) : ℕ) : ℝ) ≤ Real.exp (Vlog + 2 * E + 6) ∧
      η⁻¹ ≤ Real.exp (Vlog + 3 * E + 8) ∧
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
          ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤ Real.exp (-E) := by
  sorry

end Erdos3
end
end OAI
