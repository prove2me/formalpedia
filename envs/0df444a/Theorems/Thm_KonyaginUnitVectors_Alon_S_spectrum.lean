-- Prove2me | Theorems.Thm_KonyaginUnitVectors_Alon_S_spectrum
-- name    : KonyaginUnitVectors.Alon.S_spectrum
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:13:34.828485+00:00
-- url     : https://prove2.me/theorems/83311da4-605f-4ea4-8dd1-c0044383809f
-- title:
--   Spectral lower bound for the connection set S
-- statement:
--   Throughout, $F$ is a finite field of characteristic $2$ with $q$ elements, regarded as an algebra over $\mathbb F_2$ (for example $\mathrm{GF}(2^k)$), $\mathrm{Tr}:F\to\mathbb F_2$ is the absolute trace, and $\psi(y)=(-1)^{\mathrm{Tr}(y)}\in\{1,-1\}$ is the associated additive character of $F$.
--
--   Let $W_0,W_1\subseteq F\setminus\{0\}$ and $S=\{\gamma(x)+\gamma(y):x\in W_0,y\in W_1\}\subseteq F^3$ be as in the definition module, and assume that $(x,y)\mapsto\gamma(x)+\gamma(y)$ is injective on $W_0\times W_1$. Put $R=8\sqrt q+1$. Then for every character $\chi_w$ of $F^3$
--
--   $$\sum_{s\in S}\chi_w(s)\ \ge\ -\frac{R^2}{4},$$
--
--   and moreover
--
--   $$\bigl|\,|W_0|-|W_1|\,\bigr|\le R .$$
--
--   These bounds on the smallest eigenvalue of the Cayley graph on $F^3$ with connection set $S$, and on the sizes of the two classes, are what make the Fourier-type system of unit vectors of Alon's construction well defined and give the norm estimate.
--
--   **Formalization Note.** Injectivity is a hypothesis (it is proved separately); `chi F w s` is the character $\psi(w_1s_1+w_2s_2+w_3s_3)$ of the definition module.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction

namespace KonyaginUnitVectors.Alon

theorem S_spectrum (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (hinj : Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F)) :
    (∀ w : F × F × F, -((8 * Real.sqrt (Fintype.card F) + 1) ^ 2 / 4) ≤ ∑ s ∈ Sset F, chi F w s) ∧
    |((W0 F).card : ℝ) - ((W1 F).card : ℝ)| ≤ 8 * Real.sqrt (Fintype.card F) + 1 := by sorry

end KonyaginUnitVectors.Alon
