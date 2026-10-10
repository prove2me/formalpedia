-- Prove2me | Theorems.Thm_GravityNonRenorm_gravity_not_renormalizable
-- name    : GravityNonRenorm.gravity_not_renormalizable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:04.313854+00:00
-- url     : https://prove2.me/theorems/1fa3bc8c-21e0-4b01-9654-d131bfd0b077
-- title:
--   Gravity is not a renormalizable QFT: black-hole entropy is not CFT entropy
-- statement:
--   Let $d\ge4$ be the spacetime dimension, $G_N>0$ Newton's constant, and let $a,b,R>0$ be the data of an arbitrary $d$-dimensional conformal field theory on $\mathbb R_{\rm time}\times S^{d-1}$ obeying Eq. (29), with entropy-energy function $S_{\rm CFT}(E)=a\bigl(R\,(E/(bR^{d-1}))^{1/d}\bigr)^{d-1}$ (Eq. 30). Let $S_{\rm BH}(M)=\mathrm{Vol}(S^{d-2})\,r_H(M)^{d-2}/(4G_N)$ be the Bekenstein–Hawking entropy of the $d$-dimensional Schwarzschild black hole of mass $M$, $r_H(M)$ being the largest positive zero of $f(r)=1-\omega_{d-2}G_NM/r^{d-3}$ (Eqs. 31–32). Then it is **not** the case that
--
--   $$S_{\rm BH}(E)=\Theta\bigl(S_{\rm CFT}(E)\bigr)\qquad(E\to\infty).$$
--
--   This is the paper's main claim (Sec. V.1): the large-energy asymptotics of the density of states of gravity in asymptotically flat spacetime, dominated by black holes, is not that of any conformal field theory; hence gravity is not a renormalizable quantum field theory.
--
--   **Formalization Note** "$\sim$" in the paper is read as $\Theta$ (two-sided bounds up to positive constants for large energies). The physical inputs (UV behaviour of renormalizable QFTs, black-hole dominance, Bekenstein–Hawking formula) are encoded in the definitions; only the resulting asymptotic incompatibility is to be proved.
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm
theorem gravity_not_renormalizable (d : ℕ) (hd : 4 ≤ d) (G a b R : ℝ) (hG : 0 < G)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => flatBHEntropy d G M) =Θ[atTop]
      (fun E : ℝ => cftEntropyOfEnergy d a b R E) := by sorry
end GravityNonRenorm
