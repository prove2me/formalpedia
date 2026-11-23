-- Prove2me | Theorems.Thm_GL2QFT_Circuits_dgate_circuit_matrix_identity
-- name    : GL2QFT.Circuits.dgate_circuit_matrix_identity
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:27.948954+00:00
-- url     : https://prove2.me/theorems/9c2fc607-8b1a-4780-a20e-9508deeff2fa
-- title:
--   Exact compute–Gauss-phase–uncompute identity for Definition 6.16
-- statement:
--   Let $s(\gamma,c)$ be the computation sign of Lemma 6.28 and let $\Gamma_q$ be the normalized Gauss phase. The three-stage operator satisfies the exact matrix identity
--   $$
--   U_{\mathrm{uncompute}}(I\otimes\Gamma_q)U_{\mathrm{compute}}=\bigoplus_\gamma D_\gamma .
--   $$
--   For $c=c_\alpha$ and $\delta=\gamma-2\alpha$, the coefficient is $\chi_{\gamma-\alpha}(-1)g_q(\delta)/\sqrt q$ when $\delta\neq0$, and $1$ when $\delta=0$; the extra computation sign cancels $g_q(1)=-1$. For $c=c_\infty$ the coefficient is $1$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573, Definition 6.16 eqs. (148)-(149), p.50, Lemma 6.28, p.54, and Theorem 6.10 eq. (122), p.43.

import Definitions.Def_GL2QFT_Circuits_DgateStages

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

open GL2QFT.Supplement.AGammaGates

theorem dgate_circuit_matrix_identity (D : FieldData) :
    dgateUncomputeMat D * (frameMat (A := DgateSource D) (gaussPhase D) * dgateComputeMat D) =
      subMat (Dgate D) := by sorry
