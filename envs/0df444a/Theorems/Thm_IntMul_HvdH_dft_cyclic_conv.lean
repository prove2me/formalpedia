-- Prove2me | Theorems.Thm_IntMul_HvdH_dft_cyclic_conv
-- name    : IntMul.HvdH.dft_cyclic_conv
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:33:57.935322+00:00
-- url     : https://prove2.me/theorems/e5256d46-f779-4b9c-be73-b45d57b99f27
-- title:
--   Convolution theorem for the DFT on $\mathbb Z/N$
-- statement:
--   Let $N\ge1$ and let $u,v:\mathbb Z/N\to\mathbb C$. Write $\hat u(k)=\sum_{j\in\mathbb Z/N} e^{-2\pi i jk/N}u_j$ for the (unnormalised) discrete Fourier transform, as in Mathlib's `ZMod.dft`, and $(u*v)_m=\sum_{j\in\mathbb Z/N}u_j\,v_{m-j}$ for cyclic convolution. Then for every $k$,
--   $$\widehat{u*v}(k)=\hat u(k)\,\hat v(k).$$
--
--   This is equation (2.1) / §2.4 of Harvey–van der Hoeven: it is how the $O(n\log n)$ algorithm turns a cyclic convolution (an integer product after chunking) into pointwise products of DFTs.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 5.3

import Mathlib

namespace IntMul.HvdH
theorem dft_cyclic_conv {N : ℕ} [NeZero N] (u v : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun m => ∑ j, u j * v (m - j)) k = ZMod.dft u k * ZMod.dft v k := by sorry
end IntMul.HvdH
