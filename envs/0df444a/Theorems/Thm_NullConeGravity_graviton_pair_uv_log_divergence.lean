-- Prove2me | Theorems.Thm_NullConeGravity_graviton_pair_uv_log_divergence
-- name    : NullConeGravity.graviton_pair_uv_log_divergence
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T14:12:55.579922+00:00
-- url     : https://prove2.me/theorems/cbc3f833-e25b-4c29-8467-73fca1b3c2c9
-- title:
--   Logarithmic UV divergence of the perturbative expansion
-- statement:
--   Expanding the graviton-pair phase in $G_N$ before summing over radial modes produces a logarithmic ultraviolet divergence in the cubic coefficient. Write $s=\mathscr A/(4G_N\hbar)$ and $c=4\hbar/\mathscr A=1/(sG_N)$. The finite-$N$ connected overlap, as a function of $g=G_N$, is $F_N(g)=\frac{c^2g^2}{2}\sum_{k=1}^{N}\frac{e^{-2ikcg}}{k^2}$. The milestone asserts two facts. First, its third derivative at the origin is $F_N'''(0)=-6i\,c^3\sum_{k=1}^{N}\frac1k$, equivalently $\frac{G_N^3}{3!}\,\partial_{G_N}^3 F_N\big|_{0}=-\frac{i}{s^3}\sum_{k=1}^{N}\frac1k$, which is the cubic term of Eq. (4.34). Second, the harmonic sum diverges logarithmically, $\big(\sum_{k=1}^{N}\frac1k\big)/\log N\to1$. Together these show that the order-$G_N^3$ coefficient grows like $\log N$, even though the resummed amplitude (the previous milestone) is finite at every $s>0$.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924, Section 4.4, Eq. (4.34) (label bfq:radial-pair-uv-term)

import Mathlib

namespace NullConeGravity
theorem graviton_pair_uv_log_divergence (c : ℝ) :
    (∀ N : ℕ, iteratedDeriv 3
        (fun g : ℝ => ((c^2 * g^2 / 2 : ℝ) : ℂ) *
            Finset.sum (Finset.range N) (fun k : ℕ =>
                Complex.exp (-2 * Complex.I * (k + 1 : ℂ) * (c : ℂ) * (g : ℂ)) / (k + 1 : ℂ)^2)) 0
        = -6 * Complex.I * (c : ℂ)^3 * Finset.sum (Finset.range N) (fun k : ℕ => 1 / (k + 1 : ℂ))) ∧
    Filter.Tendsto (fun N : ℕ => Finset.sum (Finset.range N) (fun k : ℕ => (1 : ℝ) / (k + 1)) / Real.log N)
        Filter.atTop (nhds 1) := by sorry
end NullConeGravity
