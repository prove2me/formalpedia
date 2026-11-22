-- Prove2me | Theorems.Thm_MixedCloning_Optimal_wss_normalization
-- name    : MixedCloning.Optimal.wss_normalization
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T04:22:48.801573+00:00
-- url     : https://prove2.me/theorems/d628c448-e633-4627-820d-8ac61cde3f70
-- title:
--   Weak Schur sampling weights of $1^r/r$ sum to one (RSK count)
-- statement:
--   Let $n\ge0$ and $r\ge0$ be integers. For a partition $\lambda\vdash n$ let $f^\lambda=\dim(P_\lambda)$ be the number of standard Young tableaux of shape $\lambda$. Let $s_\lambda(1^r)$ be the number of semistandard Young tableaux of shape $\lambda$ with entries in $\{1,\dots,r\}$, that is, the Schur polynomial evaluated at $x_1=\dots=x_r=1$. Then
--
--   $$\sum_{\substack{\lambda\vdash n\\ \ell(\lambda)\le r}} f^\lambda\, s_\lambda(1^r)\;=\;r^n .$$
--
--   Equivalently, for $r\ge1$ the weak Schur sampling weights $\Pr[\lambda]=\dim(P_\lambda)\,s_\lambda(1^r)/r^n$ of $\mathrm{WSS}_n(1^r/r)$ sum to $1$. Bijectively, this is the RSK correspondence for words. A word $w\in[r]^n$ corresponds to a pair $(P,Q)$ of tableaux of the same shape $\lambda\vdash n$, where $P$ is semistandard with entries in $[r]$ and $Q$ is standard.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders and counts
--   - specialization: the symmetric-function identity $h_1^n=\sum_{\lambda\vdash n}f^\lambda s_\lambda$ → its evaluation at $x=(1^r,0,0,\dots)$, with the sum restricted to $\ell(\lambda)\le r$; reason: $h_1^n(1^r)=r^n$, $s_\lambda(1^r)$ counts SSYT with entries in $[r]$, and $s_\lambda(1^r)=0$ when $\ell(\lambda)>r$
--   - form: normalization of probabilities → identity multiplied by $r^n$; reason: avoids division, and it also holds at $r=0$ (both sides are $1$ for $n=0$ and $0$ for $n\ge1$)
-- source:
--   R. P. Stanley, Enumerative Combinatorics, Vol. 2, Cambridge Univ. Press, 1999 (doi:10.1017/CBO9780511609589), Ch. 7: Corollary 7.12.5, eq. (7.47) h_1^n = sum_{lambda |- n} f^lambda s_lambda, p. 324 (its bijective proof is RSK, Theorem 7.11.5, p. 319, applied to N-matrices with col(A) = (1^n), i.e. words); s_lambda as the SSYT generating function: Definition 7.10.1, p. 310. Used in Grinko–Fanizza–Scharnhorst–Spilecki, Optimal cloning of mixed states: PDF p. 15 (weak Schur sampling outputs lambda with probability dim(P_lambda) s_lambda(rho)) and PDF p. 18 (lambda ~ WSS_n(1^r/r) has probability dim(P_lambda) dim(Q^r_lambda)/r^n for l(lambda) <= r).

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem wss_normalization (n r : ℕ) :
    ∑ L ∈ partitions n r, (spechtDim L : ℝ) * schurCount L r = (r : ℝ)^n := by sorry

end MixedCloning.Optimal
