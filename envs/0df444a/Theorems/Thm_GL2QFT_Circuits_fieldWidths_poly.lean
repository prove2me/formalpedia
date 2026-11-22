-- Prove2me | Theorems.Thm_GL2QFT_Circuits_fieldWidths_poly
-- name    : GL2QFT.Circuits.fieldWidths_poly
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:56.028183+00:00
-- url     : https://prove2.me/theorems/054a708e-e93f-45e0-b2b1-955a7543aa48
-- title:
--   Polynomial-time computability of field register widths from `encData`
-- statement:
--   There exist polynomial-time computable string functions reading the self-delimiting binary encoding `D.encData` of any field instance $D$ and outputting the unary codes `encNat` of the label width `D.labW`, the tagged-register width `(D.r + 1) * D.labW`, the double tagged-register width `(D.r + 1) * D.labW + (D.r + 1) * D.labW`, and the coset-tag width `1 + (D.r + 1) * D.labW`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Remark 6.3 & §6.4.1 (pp. 34, 41), extracting register dimensions from $D$

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem fieldWidths_poly : (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat D.labW) ∧ (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat ((D.r + 1) * D.labW)) ∧ (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat ((D.r + 1) * D.labW + (D.r + 1) * D.labW)) ∧ (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (1 + (D.r + 1) * D.labW)) ∧ (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (2 * D.labW)) ∧ (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (5 * D.labW)) := by sorry

end Circuits
end GL2QFT
