-- Prove2me | Theorems.Thm_MatMulDS_lemma_4_2
-- name    : MatMulDS.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:02:29.195594+00:00
-- url     : https://prove2.me/theorems/6c346a57-65d1-49ee-90ab-87f1d831935b
-- title:
--   Lemma 4.2 — lifting a thin data structure by rectangular products
-- statement:
--   Let $\mathcal D_{\mathrm{thin}}$ be a bilinear data structure for multiplying $N_{\mathrm{thin}}\times D_{\mathrm{thin}}$ and $D_{\mathrm{thin}}\times N_{\mathrm{thin}}$ matrices, with encoding complexity $T_{\mathrm{enc}}$, $P_{\mathrm{pre}}$ precomputed products, storage complexity $T_{\mathrm{box}}$ and query time $T_{\mathrm{query}}$. Let $\lambda_{\mathrm{out}},\lambda_{\mathrm{in}}\ge1$ and set $N=\lambda_{\mathrm{out}}N_{\mathrm{thin}}$, $D=\lambda_{\mathrm{in}}D_{\mathrm{thin}}$. Then there is a bilinear data structure for multiplying $N\times D$ and $D\times N$ matrices with
--   $$T^{\mathrm{new}}_{\mathrm{pre}}\le\lambda_{\mathrm{out}}\lambda_{\mathrm{in}}T_{\mathrm{enc}}+\mathrm{MM}(\lambda_{\mathrm{out}},\lambda_{\mathrm{in}},\lambda_{\mathrm{out}})P_{\mathrm{pre}}+\lambda_{\mathrm{out}}^2T_{\mathrm{box}},\qquad T^{\mathrm{new}}_{\mathrm{query}}\le\lambda_{\mathrm{in}}T_{\mathrm{query}}.$$
--
--   This reduces thick instances to thin ones with a batched rectangular product.
--
--   Differences from the source:
--   - reading: real $\lambda_{\mathrm{out}},\lambda_{\mathrm{in}}\ge1$ → positive integers; reason: the proof splits into $\lambda$ strips, $\mathrm{MM}$ takes integers, and p.16 says parameters are rounded "without explicitly writing this out"
--   - reading: "we can construct" a data structure of uniform circuits → one structure, with sizes and correctness; no uniformity clause; reason: $\mathrm{MM}$ is a minimum over all bilinear algorithms, which need not be uniform; the uniform version is in Lemma 4.3 and Theorem 7.3, where the family exists
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma 4.2, eqs. (4.4), (4.5), pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_MatMulDS_BilinearDS
import Definitions.Def_MatMulDS_MM

set_option autoImplicit false

namespace MatMulDS

/-- **Lemma 4.2 (Lifting Data Structures), pp.16–17** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `Dthin` be a bilinear data
structure for `Nthin × Dthin` and `Dthin × Nthin` matrices, and set `N = λout Nthin` and `D = λin Dthin`. Then we can construct a new bilinear data structure for `N × D` and `D × N`
matrices with `T^new_pre ≤ λout λin Tenc + MM(λout, λin, λout) Ppre + λout² Tbox`, (4.4), and `T^new_query ≤ λin Tquery`, (4.5).

**Formalization Note.** `λout`, `λin` are positive integers: the proof splits into `λ` strips and `MM` takes integers, and §4.2, p.16, says "We also round the parameters N and D as
needed to the nearest integer without explicitly writing this out". The lemma is about one structure, so it says nothing on uniformity; `MM` is a minimum over all bilinear algorithms, and
the uniform version is in Lemma 4.3 and Theorem 7.3. -/
theorem lemma_4_2 {F : Type} [Field F] {Nthin Dthin : ℕ} (S : BilinearDS F Nthin Dthin) (lout lin : ℕ)
    (hout : 1 ≤ lout) (hin : 1 ≤ lin) :
    ∃ S' : BilinearDS F (lout * Nthin) (lin * Dthin),
      S'.Tpre ≤ lout * lin * S.Tenc + MM F lout lin lout * S.Ppre + lout ^ 2 * S.Tbox ∧
      S'.Tquery ≤ lin * S.Tquery := by sorry

end MatMulDS
