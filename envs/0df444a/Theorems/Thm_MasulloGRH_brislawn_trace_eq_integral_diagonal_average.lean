-- Prove2me | Theorems.Thm_MasulloGRH_brislawn_trace_eq_integral_diagonal_average
-- name    : MasulloGRH.brislawn_trace_eq_integral_diagonal_average
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:43:22.155896+00:00
-- url     : https://prove2.me/theorems/831f5079-6579-4dc3-9d0f-f6d958b03c6e
-- title:
--   Brislawn's trace theorem on $\mathbb R^n$: $\operatorname{Trace}(T)=\int\widetilde k(x,x)\,dx$ for the cube-averaged kernel $\widetilde k$ of a trace class operator $T$ on $L^2(\mathbb R^n)$
-- statement:
--   **Brislawn's trace theorem (Euclidean case).** Let $n\ge 0$ and let $T$ be a nuclear (trace class) operator on $L^2(\mathbb R^n)$ with Lebesgue measure. So $Tu=\sum_m\langle x_m,u\rangle\,y_m$ for some sequences with $\sum_m\|x_m\|\,\|y_m\|<\infty$, and
--   $$\operatorname{Trace}(T)=\sum_{i}\langle e_i,Te_i\rangle$$
--   for an orthonormal basis $(e_i)$, with the inner product linear in the second variable. Let $k\in L^2(\mathbb R^n\times\mathbb R^n)$ be a kernel of $T$:
--   $$(Tu)(x)=\int_{\mathbb R^n}k(x,y)\,u(y)\,dy\quad\text{for almost every }x,\ \text{for every }u\in L^2(\mathbb R^n).$$
--   For $x\in\mathbb R^n$ and $r>0$ let $Q_r(x)=\prod_{i=1}^n[x_i-r,x_i+r]$ be the closed cube of side $2r$ centred at $x$. Then for almost every $x\in\mathbb R^n$ the limit of the averages of $k$ over the cubes $Q_r(x)\times Q_r(x)$ centred at the diagonal point $(x,x)$,
--   $$\widetilde k(x,x)=\lim_{r\to0^+}\frac{1}{|Q_r(x)|^{2}}\int_{Q_r(x)\times Q_r(x)}k(y_1,y_2)\,dy_1\,dy_2 ,$$
--   exists. The function $x\mapsto\widetilde k(x,x)$ is integrable on $\mathbb R^n$, and
--   $$\int_{\mathbb R^n}\widetilde k(x,x)\,dx=\operatorname{Trace}(T).$$
--
--   For $n\ge1$ the diagonal is a null set of $\mathbb R^n\times\mathbb R^n$, so $k(x,x)$ itself has no meaning for an $L^2$ kernel. The averages $\widetilde k(x,x)$ do not depend on the representative $k$, and the theorem says that they give the correct meaning to integrating the kernel along the diagonal. The paper's Theorem 12.1.1.2(1) states an extension of this theorem to second-countable locally compact abelian groups with $D'$-sequences and weighted Haar measures; its proof (pp. 500–501) follows Brislawn's argument with the Hardy–Littlewood maximal theorem replaced by its group analogue. This is what makes the localization of the geometric trace along the diagonal (Theorem 12.1.1.3) possible.
--
--   **Formalization Note.** $\mathbb R^n$ is `Fin n → ℝ` with its sup metric. So the closed ball of radius $r$ about $(x,x)$ in the product (max) metric is $Q_r(x)\times Q_r(x)$, and the set average `⨍` divides by its volume $(2r)^{2n}=|Q_r(x)|^2$. Nuclearity and the trace are the platform notions `MasulloGRH.IsNuclearOperator` and `MasulloGRH.operatorTrace`. The latter is the sum of $\langle e_i,Te_i\rangle$ over a fixed Hilbert basis, which is the trace of a nuclear operator. The kernel is an everywhere-defined function whose uncurried form lies in $L^2$ of the product measure and represents $T$ almost everywhere, for every $u$. The diagonal values are asserted as the almost-everywhere limit, as $r\to0^+$, of the averages. The paper's generalization (locally compact abelian groups, $D'$-sequences, weights $f$) is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 499–501, proof of Theorem 12.1.1.2(1); classical reference: C. M. Brislawn, Kernels of trace class operators, Proc. Amer. Math. Soc. 104 (1988), no. 4, Thm. 3.1, p. 1185 (cited by the paper as [Bris-a, Thm. 3.1, p. 1185] and [Bris-a, pp. 1185–1186]; these page numbers belong to the paper's bibliography entry [Bris-b], the Proc. Amer. Math. Soc. article)

import Definitions.Def_MasulloGRH_HilbertNuclear

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace MasulloGRH

/-- Brislawn's trace theorem on `ℝⁿ` (cube averages): if a nuclear operator `T` on `L²(ℝⁿ)` is
the integral operator of a kernel `k ∈ L²(ℝⁿ × ℝⁿ)`, then for almost every `x` the averages of
`k` over the cubes `Q_r(x) × Q_r(x)` (the closed sup-metric balls of radius `r` about `(x, x)`)
converge as `r → 0⁺` to a limit `k̃(x, x)`; this function is integrable and its integral is the
trace of `T`. -/
theorem brislawn_trace_eq_integral_diagonal_average (n : ℕ)
    (T : Lp ℂ 2 (volume : Measure (Fin n → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)))
    (hT : IsNuclearOperator T)
    (k : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (hk : MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => k p.1 p.2) 2
      ((volume : Measure (Fin n → ℝ)).prod volume))
    (hTk : ∀ u : Lp ℂ 2 (volume : Measure (Fin n → ℝ)),
      (T u : (Fin n → ℝ) → ℂ) =ᵐ[volume] fun x => ∫ y, k x y * u y) :
    ∃ d : (Fin n → ℝ) → ℂ,
      (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        Tendsto (fun r : ℝ => ⨍ p in Metric.closedBall (x, x) r, k p.1 p.2
            ∂((volume : Measure (Fin n → ℝ)).prod volume))
          (𝓝[>] 0) (𝓝 (d x))) ∧
      Integrable d (volume : Measure (Fin n → ℝ)) ∧
      ∫ x, d x = operatorTrace T := by sorry

end MasulloGRH
