-- Prove2me | Theorems.Thm_IntMul_HvdH_lemma_2_3_multidim
-- name    : IntMul.HvdH.lemma_2_3_multidim
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:37:49.91653+00:00
-- url     : https://prove2.me/theorems/a85063ad-9b74-419e-a7e6-3e1252bfb54e
-- title:
--   Convolution formula for multidimensional cyclic convolution over $\mathbb C$
-- statement:
--   **Convolution formula on $\bigotimes_i\mathbb C^{s_i}$.** Let $s_1,\dots,s_d\ge1$ and $G=\mathbb Z/s_1\times\cdots\times\mathbb Z/s_d$, with $|G|=s_1\cdots s_d$. For $t,k\in G$ write
--   $$e(t,k)=\prod_{i=1}^d \exp\!\Big(\frac{2\pi i\,t_ik_i}{s_i}\Big).$$
--   For all $u,v:G\to\mathbb C$ and $j\in G$,
--   $$\sum_{k\in G}u_k\,v_{j-k}=\frac1{|G|}\sum_{t\in G}e(t,j)\Big(\sum_{k\in G}e(t,-k)\,u_k\Big)\Big(\sum_{k\in G}e(t,-k)\,v_k\Big).$$
--
--   With the normalised DFT $(\mathcal F u)_t=\frac1{|G|}\sum_k e(t,-k)u_k$ this is Harvey–van der Hoeven's Lemma 2.3, $\frac1{|G|}\,u*v=|G|\,\mathcal F^{-1}(\mathcal Fu\cdot\mathcal Fv)$, for the tensor product $\bigotimes_i\mathbb C^{s_i}$ with the standard roots of unity. Step (3) of Proposition 5.4 computes the $d$-dimensional cyclic convolution this way.
--
--   **Formalization Note** $G$ is `Π i : Fin d, ZMod (s i)`, and $\exp(2\pi i\,x/s)$ is Mathlib's `ZMod.stdAddChar`.
-- source:
--   D. Harvey and J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193 (2021), no. 2, 563–617, https://doi.org/10.4007/annals.2021.193.2.4, §2.4 Lemma 2.3 (convolution formula) for R = ⊗_i C^{s_i} with ω the standard roots of unity (§2.4 complex case, §2.3 tensor products); used in §5.3 step (3) and Proposition 5.3

import Mathlib
open ZMod

namespace IntMul.HvdH

theorem lemma_2_3_multidim {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)]
    (u v : (Π i, ZMod (s i)) → ℂ) (j : Π i, ZMod (s i)) :
    ∑ k, u k * v (j - k) =
      (1 / (Fintype.card (Π i, ZMod (s i)) : ℂ)) *
        ∑ t : Π i, ZMod (s i), (∏ i, stdAddChar (t i * j i)) *
          ((∑ k : Π i, ZMod (s i), (∏ i, stdAddChar (-(t i * k i))) * u k) *
           (∑ k : Π i, ZMod (s i), (∏ i, stdAddChar (-(t i * k i))) * v k)) := by sorry

end IntMul.HvdH
