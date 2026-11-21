-- Prove2me | Theorems.Thm_MasulloRepair_lower_cutoff_log_asymptotic
-- name    : MasulloRepair.lower_cutoff_log_asymptotic
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:13:28.976761+00:00
-- url     : https://prove2.me/theorems/ea4b63bf-1e8f-4143-a8f5-7c3e84c98aba
-- title:
--   Joint cutoff asymptotic $\int_{q\le M}H[\log M-\log\max(q,r)]\,d\nu=\log M\int H-\int H\log q+o(1)$ under log-integrability
-- statement:
--   **Statement.** Let $(\Omega,\nu)$ be a measure space, let $q:\Omega\to\mathbb R$ be measurable with $q>0$ $\nu$-almost everywhere, and let $H:\Omega\to\mathbb C$ be such that both $H$ and $H\log q$ are $\nu$-integrable (equivalently: $H$ is measurable and $\int|H|\,(1+|\log q|)\,d\nu<\infty$). Then
--
--   $$\int_{\{q\le M\}}H(w)\,\bigl[\log M-\log\max\{q(w),r\}\bigr]\,d\nu(w)\;=\;\log M\int_\Omega H\,d\nu-\int_\Omega H\log q\,d\nu+o(1)$$
--
--   as $M\to+\infty$ and $r\to0^+$ **jointly**: the difference of the two sides tends to $0$ along the product filter $\{M\to+\infty\}\times\{r\to0^+\}$. No relation between $M$ and $r$ is needed.
--
--   **Where this sits in the manuscript.** In the proof of Theorem 12.4.1.1 (S-local trace calculation), equations (12.4.1.23)–(12.4.1.24) on p. 518 reduce the diagonal integral of the kernel to
--
--   $$\int_{|w|_{F,S}\le\lambda\lambda'}\eta_\xi(w)\,\bigl(\log(\lambda\lambda')-\log|w|_{F,S}\bigr)\,d\nu_S(w),$$
--
--   where the bracket is the logarithmic volume of $\{x:\ |w|/\lambda'\le|x|\le\lambda\}$. Footnote 2 on p. 514 announces that the cutoff is to be replaced by a smoothing of $\mathbf 1_{[1/\lambda'',\lambda]}$ "with $\lambda''$ not tied to $\lambda$", and that one must then "study the convergence of the integral in (12.4.1.23), with $\log|w|_{F,S}$ replaced by $\log\max\{|w|_{F,S}/\lambda',1/\lambda''\}$, as $\lambda',\lambda''\to+\infty$". With the lower cutoff the bracket becomes $\log\lambda-\log\max\{|w|/\lambda',1/\lambda''\}=\log(\lambda\lambda')-\log\max\{|w|,\lambda'/\lambda''\}$, so the integral is the left-hand side above with
--
--   $$q=|\cdot|_{F,S},\qquad H=\eta_\xi,\qquad M=\lambda\lambda',\qquad r=\lambda'/\lambda''.$$
--
--   The manuscript states neither an integrability hypothesis on $\eta_\xi\log|\cdot|_{F,S}$ nor a relation between the cutoffs. This theorem is a **repair** of that step: it gives a precise sufficient condition, namely log-integrability of the integrand together with $\lambda\lambda'\to+\infty$ and $\lambda'/\lambda''\to0^+$ (composition of the stated limit with $(\lambda,\lambda',\lambda'')\mapsto(\lambda\lambda',\lambda'/\lambda'')$). The printed case without lower cutoff corresponds to $r=0$.
--
--   **Scope.** This is a statement about one fixed integrand. It does not treat the sum over $\xi\in\mathcal O_{F,S}^\times$ (which needs its own uniform tail bound), it does not verify that $\eta_\xi\log|\cdot|_{F,S}$ is integrable in the adelic setting, and it does not establish Theorem 12.4.1.1.
--
--   **Formalization notes.** The complex integrals are Bochner integrals; $\log$ is the real logarithm, coerced to $\mathbb C$. The hypotheses are `Integrable H ν` and `Integrable (fun w => H w * log (q w)) ν`; the limit is `Tendsto … (atTop ×ˢ 𝓝[>] 0) (𝓝 0)` for the function of $p=(M,r)$ equal to the left side minus the two main terms.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, proof of Theorem 12.4.1.1, footnote 2 on p. 514 and equations (12.4.1.23)-(12.4.1.24), p. 518

import Mathlib

open MeasureTheory Filter Topology

theorem MasulloRepair.lower_cutoff_log_asymptotic
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (q : Ω → ℝ) (H : Ω → ℂ)
    (hq : Measurable q) (hqpos : ∀ᵐ w ∂ν, 0 < q w)
    (hH : Integrable H ν)
    (hHlog : Integrable (fun w => H w * (Real.log (q w) : ℂ)) ν) :
    Tendsto
      (fun p : ℝ × ℝ =>
        (∫ w in {w | q w ≤ p.1},
            H w * ((Real.log p.1 - Real.log (max (q w) p.2) : ℝ) : ℂ) ∂ν)
          - ((Real.log p.1 : ℂ) * ∫ w, H w ∂ν - ∫ w, H w * (Real.log (q w) : ℂ) ∂ν))
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by sorry
