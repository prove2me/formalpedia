-- Prove2me | Theorems.Thm_IntMul_HvdH_synGa_approx
-- name    : IntMul.HvdH.synGa_approx
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T01:27:46.788981+00:00
-- url     : https://prove2.me/theorems/77808aea-37bb-4cdb-924d-0fe169727993
-- title:
--   Fixed-point synthetic FFT error bound (Lemma 3.2)
-- statement:
--   Let $R=\mathbb C[y]/(y^r+1)$ and $t=2^e$. Let $\mathcal G_t:R^t\to R^t$ be the normalised synthetic DFT $u\mapsto\tfrac1t\hat u$, computed by the radix-2 recursion `synG` (`IntMul_HvdH_SynFFT`). Let $\tilde{\mathcal G}_t$ be its fixed-point version `synGa` at precision $p$, which rounds each halving towards zero. Then $\tilde{\mathcal G}_t$ maps the unit polydisc into itself and
--   $$\varepsilon(\tilde{\mathcal G}_t)\le\log_2 t=e.$$
--   This is the error part of Lemma 3.2 of Harvey–van der Hoeven, in the sense of `FPApprox` (`IntMul_HvdH_FPApprox`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 3.2

import Definitions.Def_IntMul_HvdH_SynFFT

namespace IntMul.HvdH
theorem synGa_approx (p r e : ℕ) : FPApprox p (synGa r e) (synG r e) e := by sorry
end IntMul.HvdH
